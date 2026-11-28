// Direct TypeScript (ts-morph Type / TypeNode) -> Ty extraction.
//
// Single source of truth for lowering TypeScript source types into LemmaScript's
// canonical `Ty` representation without round-tripping through string
// serialization or re-parsing with a scratch ts-morph SourceFile.

import { Node, SyntaxKind, type Type, type TypeNode } from "ts-morph";
import { type Ty, tyEqual } from "./typedir.js";
import type { TypeDeclInfo } from "./types.js";

export interface ErasedTypeParam {
  text: string;
  ty: Ty;
}

export interface ExtractTypeCtx {
  /** Collapsed single-variant union alias recovery: sorted property names -> alias name. */
  collapsedUnionMap?: ReadonlyMap<string, string>;
  /** Generic bounds erasure map: type parameter name -> erased text + Ty. */
  typeParamMap?: ReadonlyMap<string, ErasedTypeParam>;
  /** Accumulator for synthesized `T[] | U` array-union and `Opaque_*` TypeDeclInfo entries. */
  synthArrayUnions?: TypeDeclInfo[] | null;
  /** Returns true when a ts-morph Type is a safe-integer numeric const enum. */
  isConstEnum?: (type: Type) => boolean;
}

const EMPTY_CTX: ExtractTypeCtx = {};

/** Sanitize an arbitrary type-string fragment for use inside a generated identifier. */
export function sanitizeSynthFragment(s: string): string {
  return s.replace(/[^A-Za-z0-9]+/g, "_").replace(/^_+|_+$/g, "");
}

/** Canonical name for a synthesized `T[] | U` discriminated union. */
export function synthArrayUnionName(elemName: string, otherName: string): string {
  return `ArrayOf_${sanitizeSynthFragment(elemName)}_Or_${sanitizeSynthFragment(otherName)}`;
}

/** Register a synthesized `T[] | U` discriminated union if not already present. */
export function registerSynthArrayUnion(
  synthDecls: TypeDeclInfo[],
  elemName: string,
  elemTy: Ty,
  otherName: string,
  otherTy: Ty,
): string {
  const synthName = synthArrayUnionName(elemName, otherName);
  if (!synthDecls.some(d => d.name === synthName)) {
    synthDecls.push({
      name: synthName,
      kind: "discriminated-union",
      discriminant: "__isArray__",
      variants: [
        { name: "ArrayBranch", fields: [{ name: "arr", tsType: `${elemName}[]`, type: { kind: "array", elem: elemTy } }] },
        { name: "NonArrayBranch", fields: [{ name: "val", tsType: otherName, type: otherTy }] },
      ],
    });
  }
  return synthName;
}

/** Register an opaque union type for an unmodelable multi-member union. */
export function registerSynthOpaque(
  memberNames: string[],
  synthDecls: TypeDeclInfo[] | null | undefined,
): string {
  const name = `Opaque_${memberNames.map(sanitizeSynthFragment).join("_or_")}`;
  if (synthDecls && !synthDecls.some(d => d.name === name)) {
    synthDecls.push({ name, kind: "opaque" });
  }
  return name;
}

/** Merge null / undefined optionality flags with an inner Ty, flattening nested
 *  `optional` / `nullish` wrappers so `optional(T, null) | undefined` becomes
 *  `nullish(T)` and repeated `undefined` never double-wraps. */
export function wrapNullability(inner: Ty, hasNull: boolean, hasUndef: boolean): Ty {
  let payload = inner;
  let mergedNull = hasNull;
  let mergedUndef = hasUndef;
  while (payload.kind === "optional" || payload.kind === "nullish") {
    if (payload.kind === "nullish") {
      mergedNull = true;
      mergedUndef = true;
      payload = payload.inner;
    } else {
      if (payload.absent === "null") mergedNull = true;
      else mergedUndef = true;
      payload = payload.inner;
    }
  }
  if (payload.kind === "null") {
    if (mergedUndef) return { kind: "nullish", inner: { kind: "void" } };
    return payload;
  }
  if (payload.kind === "void") {
    if (mergedNull) return { kind: "nullish", inner: { kind: "void" } };
    return payload;
  }
  if (mergedNull && mergedUndef) return { kind: "nullish", inner: payload };
  if (mergedNull) return { kind: "optional", inner: payload, absent: "null" };
  if (mergedUndef) return { kind: "optional", inner: payload };
  return payload;
}

/** Apply generic bounds erasure (`<T extends B>`) to an already-extracted Ty. */
export function eraseGenericTy(ty: Ty, typeParamMap: ReadonlyMap<string, ErasedTypeParam>): Ty {
  if (typeParamMap.size === 0) return ty;
  switch (ty.kind) {
    case "user": {
      const hit = typeParamMap.get(ty.name);
      if (hit) return hit.ty;
      return ty;
    }
    case "array":
      return { kind: "array", elem: eraseGenericTy(ty.elem, typeParamMap) };
    case "set":
      return { kind: "set", elem: eraseGenericTy(ty.elem, typeParamMap) };
    case "map":
      return {
        kind: "map",
        key: eraseGenericTy(ty.key, typeParamMap),
        value: eraseGenericTy(ty.value, typeParamMap),
      };
    case "optional":
      return ty.absent === "null"
        ? { kind: "optional", inner: eraseGenericTy(ty.inner, typeParamMap), absent: "null" }
        : { kind: "optional", inner: eraseGenericTy(ty.inner, typeParamMap) };
    case "nullish":
      return { kind: "nullish", inner: eraseGenericTy(ty.inner, typeParamMap) };
    case "tuple":
      return { kind: "tuple", elems: ty.elems.map(e => eraseGenericTy(e, typeParamMap)) };
    case "fn":
      return {
        kind: "fn",
        params: ty.params.map(p => eraseGenericTy(p, typeParamMap)),
        result: eraseGenericTy(ty.result, typeParamMap),
      };
    default:
      return ty;
  }
}

/** True when a TypeNode is or contains an `IndexedAccessType` (`T["k"]`, `T["k"][number]`).
 *  Syntactic extraction cannot resolve indexed access, so callers fall back to the
 *  type checker's resolved `Type`. */
export function hasIndexedAccessType(tn: TypeNode): boolean {
  return Node.isIndexedAccessTypeNode(tn)
    || tn.getFirstDescendantByKind(SyntaxKind.IndexedAccessType) !== undefined;
}

function tupleTyFromElems(elems: Ty[]): Ty {
  if (elems.length === 0) return { kind: "array", elem: { kind: "unknown" } };
  if (elems.every(e => tyEqual(e, elems[0]))) return { kind: "array", elem: elems[0] };
  return { kind: "tuple", elems };
}

/** Lower a builtin collection or wrapper name (`Array`, `ReadonlyArray`, `Set`,
 *  `ReadonlySet`, `Map`, `ReadonlyMap`, `Record`, `Readonly`) to a canonical
 *  `Ty`, or `null` when the name and arity do not match. */
function lowerBuiltinCollection(name: string, args: Ty[]): Ty | null {
  if ((name === "Array" || name === "ReadonlyArray") && args.length === 1) {
    return { kind: "array", elem: args[0] };
  }
  if ((name === "Set" || name === "ReadonlySet") && args.length === 1) {
    return { kind: "set", elem: args[0] };
  }
  if ((name === "Map" || name === "ReadonlyMap" || name === "Record") && args.length === 2) {
    return { kind: "map", key: args[0], value: args[1] };
  }
  if (name === "Readonly" && args.length === 1) {
    return args[0];
  }
  return null;
}

/** Synthesize `ArrayOf_<Elem>_Or_<Other>` for a 2-arm syntactic union `T[] | U`
 *  (where U is not array/null/undefined). Applies `ctx.typeParamMap` erasure so
 *  bounded generic type parameters never leak into synthesized datatype names
 *  or branch fields. */
export function trySynthArrayUnionFromNodes(arms: TypeNode[], ctx: ExtractTypeCtx): string | null {
  if (!ctx.synthArrayUnions || arms.length !== 2) return null;
  const arrIdx = arms.findIndex(m => m.getType().isArray());
  if (arrIdx === -1) return null;
  const other = arms[1 - arrIdx];
  const ot = other.getType();
  if (ot.isArray() || ot.isUndefined() || ot.isNull()) return null;
  const arrNode = arms[arrIdx];
  const elemNode = Node.isArrayTypeNode(arrNode) ? arrNode.getElementTypeNode() : undefined;
  const rawElemName = elemNode
    ? elemNode.getText()
    : typeToTsString(arrNode.getType().getArrayElementTypeOrThrow(), ctx);
  const rawElemTy = elemNode
    ? lowerTypeNode(elemNode, ctx)
    : lowerCheckerType(arrNode.getType().getArrayElementTypeOrThrow(), ctx, new Set());
  const rawOtherName = other.getText();
  const rawOtherTy = lowerTypeNode(other, ctx);
  const elemName = eraseTypeText(rawElemName, ctx.typeParamMap);
  const otherName = eraseTypeText(rawOtherName, ctx.typeParamMap);
  const elemTy = ctx.typeParamMap && ctx.typeParamMap.size > 0
    ? eraseGenericTy(rawElemTy, ctx.typeParamMap)
    : rawElemTy;
  const otherTy = ctx.typeParamMap && ctx.typeParamMap.size > 0
    ? eraseGenericTy(rawOtherTy, ctx.typeParamMap)
    : rawOtherTy;
  return registerSynthArrayUnion(ctx.synthArrayUnions, elemName, elemTy, otherName, otherTy);
}

/** Synthesize `ArrayOf_<Elem>_Or_<Other>` for a 2-member checker union `T[] | U`
 *  (where U is not array/null/undefined). */
function trySynthArrayUnionFromTypes(
  unionTypes: Type[],
  ctx: ExtractTypeCtx,
  visited: Set<Type>,
): string | null {
  if (!ctx.synthArrayUnions || unionTypes.length !== 2) return null;
  const [m0, m1] = unionTypes;
  const arrayMember = m0.isArray() ? m0 : (m1.isArray() ? m1 : null);
  const otherMember = arrayMember === m0 ? m1 : m0;
  if (!arrayMember || !otherMember || otherMember.isArray()
      || otherMember.isUndefined() || otherMember.isNull()) {
    return null;
  }
  const elemType = arrayMember.getArrayElementTypeOrThrow();
  const rawElemName = typeToTsString(elemType, ctx);
  const rawOtherName = typeToTsString(otherMember, ctx);
  const rawElemTy = lowerCheckerType(elemType, ctx, visited);
  const rawOtherTy = lowerCheckerType(otherMember, ctx, visited);
  const elemName = eraseTypeText(rawElemName, ctx.typeParamMap);
  const otherName = eraseTypeText(rawOtherName, ctx.typeParamMap);
  const elemTy = ctx.typeParamMap && ctx.typeParamMap.size > 0
    ? eraseGenericTy(rawElemTy, ctx.typeParamMap)
    : rawElemTy;
  const otherTy = ctx.typeParamMap && ctx.typeParamMap.size > 0
    ? eraseGenericTy(rawOtherTy, ctx.typeParamMap)
    : rawOtherTy;
  return registerSynthArrayUnion(ctx.synthArrayUnions, elemName, elemTy, otherName, otherTy);
}

/** Format a checker `Type` as a TS type string (used for `RawIR` `tsType` metadata,
 *  generic user-type spellings like `Foo<A, B>`, and `Opaque_*` naming). */
export function typeToTsString(type: Type, ctx: ExtractTypeCtx = EMPTY_CTX): string {
  if (ctx.isConstEnum?.(type)) return "number";
  if (type.isUndefined()) return "undefined";
  if (type.isNull()) return "null";
  if (type.isNumber() || type.isNumberLiteral()) return "number";
  if (type.isBigInt() || type.isBigIntLiteral()) return "bigint";
  if (type.isString() || type.isStringLiteral()) return "string";
  // TS expands `boolean` to `false | true`; normalize back so union deduping
  // keeps a single `boolean`.
  if (type.isBoolean() || type.isBooleanLiteral()) return "boolean";
  const aliasSym = type.getAliasSymbol();
  if (aliasSym) {
    const name = aliasSym.getName();
    const args = type.getAliasTypeArguments();
    if (args.length > 0) return `${name}<${args.map(t => typeToTsString(t, ctx)).join(", ")}>`;
    return name;
  }
  if (type.isUnion()) {
    const unionTypes = type.getUnionTypes();
    const nullish = unionTypes.filter(t => t.isNull() || t.isUndefined());
    if (nullish.length > 0) {
      const inner = type.getNonNullableType();
      if (inner.isUnion() && inner.getAliasSymbol()) {
        return [typeToTsString(inner, ctx), ...nullish.map(t => typeToTsString(t, ctx))].join(" | ");
      }
    }
    const synth = trySynthArrayUnionFromTypes(unionTypes, ctx, new Set());
    if (synth) return synth;
    const parts = [...new Set(unionTypes.map(t => typeToTsString(t, ctx)))];
    const real = parts.filter(p => p !== "undefined" && p !== "null");
    if (real.length <= 1) return parts.join(" | ");
    const opaque = registerSynthOpaque(real, ctx.synthArrayUnions);
    const hasNull = parts.includes("null");
    const hasUndef = parts.includes("undefined");
    if (hasNull && hasUndef) return `${opaque} | null | undefined`;
    if (hasNull) return `${opaque} | null`;
    if (hasUndef) return `${opaque} | undefined`;
    return opaque;
  }
  if (type.isTuple()) {
    return `[${type.getTupleElements().map(t => typeToTsString(t, ctx)).join(", ")}]`;
  }
  if (type.isArray()) {
    const elem = type.getArrayElementTypeOrThrow();
    return `${typeToTsString(elem, ctx)}[]`;
  }
  const symbol = type.getSymbol() ?? type.getAliasSymbol();
  if (symbol) {
    const name = symbol.getName();
    if (name === "__type" && ctx.collapsedUnionMap && ctx.collapsedUnionMap.size > 0) {
      const props = type.getProperties().map(p => p.getName()).sort().join(",");
      const alias = ctx.collapsedUnionMap.get(props);
      if (alias) return alias;
    }
    const typeArgs = type.getTypeArguments();
    if (typeArgs.length > 0) {
      return `${name}<${typeArgs.map(t => typeToTsString(t, ctx)).join(", ")}>`;
    }
    return name;
  }
  return type.getText();
}

/** Extract a canonical `Ty` directly from a syntactic ts-morph `TypeNode`.
 *  Preserves syntactic information the checker erases:
 *   - `| null` / `| undefined` in non-strict projects
 *   - type alias names (`ListId | undefined`)
 *   - inline string-literal union `values` (`"a" | "b"`)
 *   - `TypePredicate` (`x is T` -> `bool`)
 *   - `readonly T[]` / `readonly [A, B]`
 *   - `T[] | U` synthesized array unions (when `ctx.synthArrayUnions` is set)
 *  When `tn` contains an `IndexedAccessType`, falls back to `extractTy` on the
 *  resolved checker `Type`. */
export function extractTyFromNode(
  tn: TypeNode,
  resolvedType?: Type,
  ctx: ExtractTypeCtx = EMPTY_CTX,
): Ty {
  if (hasIndexedAccessType(tn)) {
    return extractTy(resolvedType ?? tn.getType(), undefined, ctx);
  }
  const ty = lowerTypeNode(tn, ctx);
  return ctx.typeParamMap && ctx.typeParamMap.size > 0
    ? eraseGenericTy(ty, ctx.typeParamMap)
    : ty;
}

export function eraseTypeText(text: string, typeParamMap?: ReadonlyMap<string, ErasedTypeParam>): string {
  if (!typeParamMap || typeParamMap.size === 0) return text;
  if (text.includes(" | ")) {
    const arms = [...new Set(text.split(" | ").map(a => eraseTypeText(a.trim(), typeParamMap)))];
    return arms.length === 1 ? arms[0] : arms.join(" | ");
  }
  if (text.endsWith("[]")) return eraseTypeText(text.slice(0, -2), typeParamMap) + "[]";
  return typeParamMap.get(text)?.text ?? text;
}

function unwrapParenTypeNode(tn: TypeNode): TypeNode {
  let cur = tn;
  while (Node.isParenthesizedTypeNode(cur)) cur = cur.getTypeNode();
  return cur;
}

function lowerTypeNode(tn: TypeNode, ctx: ExtractTypeCtx): Ty {
  if (Node.isParenthesizedTypeNode(tn)) return lowerTypeNode(tn.getTypeNode(), ctx);
  // `readonly T[]`, `readonly [A, B]` — Readonly TypeOperator wrapping the inner type.
  if (Node.isTypeOperatorTypeNode(tn) && tn.getOperator() === SyntaxKind.ReadonlyKeyword) {
    return lowerTypeNode(tn.getTypeNode(), ctx);
  }
  if (tn.getKind() === SyntaxKind.TypePredicate) return { kind: "bool" };

  if (Node.isUnionTypeNode(tn)) {
    const arms = tn.getTypeNodes();
    // `T[] | U` synthesis on syntactic unions (preserving alias spellings like `Part[] | string`).
    const synthName = trySynthArrayUnionFromNodes(arms, ctx);
    if (synthName) return { kind: "user", name: synthName };

    const isBoolLit = (a: TypeNode) => {
      const u = unwrapParenTypeNode(a);
      return Node.isLiteralTypeNode(u)
        && (u.getLiteral().getKind() === SyntaxKind.TrueKeyword || u.getLiteral().getKind() === SyntaxKind.FalseKeyword);
    };
    const isNullNode = (a: TypeNode) => {
      const u = unwrapParenTypeNode(a);
      return u.getKind() === SyntaxKind.NullKeyword
        || (Node.isLiteralTypeNode(u) && u.getLiteral().getKind() === SyntaxKind.NullKeyword);
    };
    const isUndefNode = (a: TypeNode) => unwrapParenTypeNode(a).getKind() === SyntaxKind.UndefinedKeyword;
    const isNullish = (a: TypeNode) => isNullNode(a) || isUndefNode(a);

    const hasNull = arms.some(isNullNode);
    const hasUndef = arms.some(isUndefNode);

    const hasTrueLit = arms.some(a => Node.isLiteralTypeNode(a) && a.getLiteral().getKind() === SyntaxKind.TrueKeyword);
    const hasFalseLit = arms.some(a => Node.isLiteralTypeNode(a) && a.getLiteral().getKind() === SyntaxKind.FalseKeyword);
    const collapseBool = hasTrueLit && hasFalseLit;
    const normalized: ({ node: TypeNode } | { syntheticBool: true })[] = collapseBool
      ? [{ syntheticBool: true } as const, ...arms.filter(a => !isBoolLit(a)).map(node => ({ node }))]
      : arms.map(node => ({ node }));

    if (normalized.length === 1 && "syntheticBool" in normalized[0]) return { kind: "bool" };

    const nonNullish = normalized.filter(a => "syntheticBool" in a || !isNullish(a.node));
    if (nonNullish.length === 0) {
      if (hasNull && hasUndef) return { kind: "nullish", inner: { kind: "void" } };
      if (hasNull) return { kind: "null" };
      return { kind: "void" };
    }

    // Inline string-literal union (`"a" | "b"`): preserve literal values so
    // `rec[k]` can lower to an equality chain.
    const isStrLit = (a: { node: TypeNode } | { syntheticBool: true }) =>
      !("syntheticBool" in a)
      && Node.isLiteralTypeNode(a.node)
      && a.node.getLiteral().getKind() === SyntaxKind.StringLiteral;
    if (nonNullish.length >= 2 && nonNullish.every(isStrLit)) {
      const values = nonNullish.map(a => {
        const lit = (a as { node: TypeNode }).node;
        const inner = Node.isLiteralTypeNode(lit) ? lit.getLiteral() : lit;
        return Node.isStringLiteral(inner) ? inner.getLiteralValue() : inner.getText();
      });
      return wrapNullability({ kind: "string", values }, hasNull, hasUndef);
    }

    // Numeric literal unions (`0 | 1 | 2`, `-1 | 0 | 1`) lower to `int`.
    if (nonNullish.length >= 2 && nonNullish.every(a => {
      if ("syntheticBool" in a) return false;
      const ty = lowerTypeNode(a.node, ctx);
      return ty.kind === "int" && !ty.big;
    })) {
      return wrapNullability({ kind: "int" }, hasNull, hasUndef);
    }

    // Deduplicate erased arms (e.g. `T | B` where `T extends B` erases to `B`).
    if (ctx.typeParamMap && ctx.typeParamMap.size > 0 && nonNullish.length >= 2) {
      const lowered = nonNullish.map(a =>
        "syntheticBool" in a ? ({ kind: "bool" } as Ty) : eraseGenericTy(lowerTypeNode(a.node, ctx), ctx.typeParamMap!),
      );
      if (lowered.every(t => tyEqual(t, lowered[0]))) {
        return wrapNullability(lowered[0], hasNull, hasUndef);
      }
    }

    if (nonNullish.length === 1) {
      const sole = nonNullish[0];
      const inner: Ty = "syntheticBool" in sole ? { kind: "bool" } : lowerTypeNode(sole.node, ctx);
      return wrapNullability(inner, hasNull, hasUndef);
    }

    // Multi-member union with a nullish arm (`A | B | undefined`).
    if (hasNull || hasUndef) {
      const restText = nonNullish
        .map(a => ("syntheticBool" in a ? "boolean" : eraseTypeText(a.node.getText(), ctx.typeParamMap)))
        .join(" | ");
      return wrapNullability({ kind: "user", name: restText }, hasNull, hasUndef);
    }
    return { kind: "user", name: eraseTypeText(tn.getText(), ctx.typeParamMap) };
  }

  if (Node.isArrayTypeNode(tn)) {
    return { kind: "array", elem: lowerTypeNode(tn.getElementTypeNode(), ctx) };
  }
  if (Node.isTupleTypeNode(tn)) {
    const elems = tn.getElements().map(e => {
      if (Node.isNamedTupleMember(e)) {
        const ty = lowerTypeNode(e.getTypeNode(), ctx);
        return e.hasQuestionToken() ? wrapNullability(ty, false, true) : ty;
      }
      if (e.getKind() === SyntaxKind.OptionalType) {
        const inner = e.getFirstChild();
        const ty: Ty = inner ? lowerTypeNode(inner as TypeNode, ctx) : { kind: "unknown" };
        return wrapNullability(ty, false, true);
      }
      return lowerTypeNode(e, ctx);
    });
    return tupleTyFromElems(elems);
  }
  if (Node.isFunctionTypeNode(tn)) {
    const params = tn.getParameters().map(p => {
      const ptn = p.getTypeNode();
      const ty: Ty = ptn ? lowerTypeNode(ptn, ctx) : { kind: "unknown" };
      return p.hasQuestionToken() ? wrapNullability(ty, false, true) : ty;
    });
    const rtn = tn.getReturnTypeNode();
    const result: Ty = rtn ? lowerTypeNode(rtn, ctx) : { kind: "void" };
    return { kind: "fn", params, result };
  }
  if (Node.isLiteralTypeNode(tn)) {
    const lit = tn.getLiteral();
    const lk = lit.getKind();
    if (lk === SyntaxKind.NullKeyword) return { kind: "null" };
    if (lk === SyntaxKind.TrueKeyword || lk === SyntaxKind.FalseKeyword) return { kind: "bool" };
    if (lk === SyntaxKind.NumericLiteral) return { kind: "int" };
    if (lk === SyntaxKind.BigIntLiteral) return { kind: "int", big: true };
    if (Node.isPrefixUnaryExpression(lit) && lit.getOperand().getKind() === SyntaxKind.NumericLiteral) {
      return { kind: "int" };
    }
    if (Node.isPrefixUnaryExpression(lit) && lit.getOperand().getKind() === SyntaxKind.BigIntLiteral) {
      return { kind: "int", big: true };
    }
  }
  switch (tn.getKind()) {
    case SyntaxKind.NumberKeyword: return { kind: "int" };
    case SyntaxKind.BigIntKeyword: return { kind: "int", big: true };
    case SyntaxKind.BooleanKeyword: return { kind: "bool" };
    case SyntaxKind.StringKeyword: return { kind: "string" };
    case SyntaxKind.NullKeyword: return { kind: "null" };
    case SyntaxKind.VoidKeyword:
    case SyntaxKind.UndefinedKeyword: return { kind: "void" };
    case SyntaxKind.UnknownKeyword:
    case SyntaxKind.AnyKeyword: return { kind: "unknown" };
  }
  if (Node.isTypeReference(tn)) {
    const name = tn.getTypeName().getText();
    const args = tn.getTypeArguments();
    if (args.length === 0) {
      const erased = ctx.typeParamMap?.get(name);
      if (erased) return erased.ty;
      if (name === "nat") return { kind: "nat" };
      if (name === "real") return { kind: "real" };
      if (name === "int") return { kind: "int" };
    }
    const loweredArgs = args.map(a => lowerTypeNode(a, ctx));
    const builtin = lowerBuiltinCollection(name, loweredArgs);
    if (builtin) return builtin;
    return { kind: "user", name: eraseTypeText(tn.getText(), ctx.typeParamMap) };
  }
  return { kind: "user", name: eraseTypeText(tn.getText(), ctx.typeParamMap) };
}

/** Extract a canonical `Ty` directly from a ts-morph `Type`, optionally using a
 *  syntactic `TypeNode` when available so non-strict nullability, type aliases,
 *  and inline string-literal unions are preserved. */
export function extractTy(
  type: Type,
  typeNode?: TypeNode,
  ctx: ExtractTypeCtx = EMPTY_CTX,
): Ty {
  if (typeNode) return extractTyFromNode(typeNode, type, ctx);
  const ty = lowerCheckerType(type, ctx, new Set());
  return ctx.typeParamMap && ctx.typeParamMap.size > 0
    ? eraseGenericTy(ty, ctx.typeParamMap)
    : ty;
}

function lowerCheckerType(type: Type, ctx: ExtractTypeCtx, visited: Set<Type>): Ty {
  if (ctx.isConstEnum?.(type)) return { kind: "int" };
  if (type.isUndefined()) return { kind: "void" };
  if (type.isNull()) return { kind: "null" };
  if (type.isVoid()) return { kind: "void" };
  if (type.isAny() || type.isUnknown()) return { kind: "unknown" };
  if (type.isNumber() || type.isNumberLiteral()) return { kind: "int" };
  if (type.isBigInt() || type.isBigIntLiteral()) return { kind: "int", big: true };
  if (type.isString() || type.isStringLiteral()) return { kind: "string" };
  if (type.isBoolean() || type.isBooleanLiteral()) return { kind: "bool" };

  // Named type alias — MUST check built-in collection/wrapper aliases
  // (especially `Record<K, V>` and `Readonly<T>`, which TS defines as type
  // aliases in lib.es5.d.ts) BEFORE returning `{ kind: "user", name }`.
  const aliasSym = type.getAliasSymbol();
  if (aliasSym) {
    const name = aliasSym.getName();
    const args = type.getAliasTypeArguments();
    if (args.length > 0) {
      if (visited.has(type)) return { kind: "user", name };
      const nextVisited = new Set(visited);
      nextVisited.add(type);
      const loweredArgs = args.map(t => lowerCheckerType(t, ctx, nextVisited));
      const builtin = lowerBuiltinCollection(name, loweredArgs);
      if (builtin) return builtin;
      return { kind: "user", name: `${name}<${args.map(t => typeToTsString(t, ctx)).join(", ")}>` };
    }
    return { kind: "user", name };
  }

  if (type.isUnion()) {
    const unionTypes = type.getUnionTypes();
    const hasNull = unionTypes.some(t => t.isNull());
    const hasUndef = unionTypes.some(t => t.isUndefined());

    // Preserve a named inner union alias under `| null` / `| undefined`
    // (e.g. `Priority | undefined` where `type Priority = "low" | "high"`).
    if (hasNull || hasUndef) {
      const inner = type.getNonNullableType();
      if (inner.isUnion() && inner.getAliasSymbol()) {
        return wrapNullability(lowerCheckerType(inner, ctx, visited), hasNull, hasUndef);
      }
    }

    // `T[] | U` synthesis: exactly two members, one array, the other not
    // array/undefined/null.
    const synthName = trySynthArrayUnionFromTypes(unionTypes, ctx, visited);
    if (synthName) return { kind: "user", name: synthName };

    const nonNullish = unionTypes.filter(t => !t.isNull() && !t.isUndefined());
    if (nonNullish.length === 0) {
      if (hasNull && hasUndef) return { kind: "nullish", inner: { kind: "void" } };
      if (hasNull) return { kind: "null" };
      return { kind: "void" };
    }

    // Boolean literal union (`false | true`, possibly with null/undefined).
    if (nonNullish.every(t => t.isBoolean() || t.isBooleanLiteral())) {
      return wrapNullability({ kind: "bool" }, hasNull, hasUndef);
    }

    // Numeric literal / const-enum union (e.g. `0 | 1 | 2`).
    if (nonNullish.every(t => t.isNumber() || t.isNumberLiteral() || !!ctx.isConstEnum?.(t))) {
      return wrapNullability({ kind: "int" }, hasNull, hasUndef);
    }

    // BigInt literal union.
    if (nonNullish.every(t => t.isBigInt() || t.isBigIntLiteral())) {
      return wrapNullability({ kind: "int", big: true }, hasNull, hasUndef);
    }

    // Inline string-literal union (`"a" | "b"`): preserve literal values so
    // record indexing (`rec[k]`) works on checker-resolved indexed access types too.
    if (nonNullish.length >= 2 && nonNullish.every(t => t.isStringLiteral())) {
      const values = nonNullish.map(t => String(t.getLiteralValue()));
      return wrapNullability({ kind: "string", values }, hasNull, hasUndef);
    }

    // Mixed string + string literals (`string | "a"` -> `string`).
    if (nonNullish.every(t => t.isString() || t.isStringLiteral())) {
      return wrapNullability({ kind: "string" }, hasNull, hasUndef);
    }

    // Single remaining real arm (or all arms lower to the same Ty).
    const loweredArms = nonNullish.map(t => lowerCheckerType(t, ctx, visited));
    if (loweredArms.every(t => tyEqual(t, loweredArms[0]))) {
      return wrapNullability(loweredArms[0], hasNull, hasUndef);
    }

    // Multi-member unmodelable union -> opaque type, preserving outer null/undefined.
    const realNames = [...new Set(nonNullish.map(t => typeToTsString(t, ctx)))]
      .filter(p => p !== "undefined" && p !== "null");
    const opaqueName = registerSynthOpaque(realNames, ctx.synthArrayUnions);
    return wrapNullability({ kind: "user", name: opaqueName }, hasNull, hasUndef);
  }

  // Tuples BEFORE arrays (tuples are assignable to Array in TS).
  if (type.isTuple()) {
    if (visited.has(type)) return { kind: "unknown" };
    const nextVisited = new Set(visited);
    nextVisited.add(type);
    const elems = type.getTupleElements().map(t => lowerCheckerType(t, ctx, nextVisited));
    return tupleTyFromElems(elems);
  }

  if (type.isArray() || type.isReadonlyArray()) {
    if (visited.has(type)) return { kind: "unknown" };
    const nextVisited = new Set(visited);
    nextVisited.add(type);
    const elem = type.getArrayElementTypeOrThrow();
    return { kind: "array", elem: lowerCheckerType(elem, ctx, nextVisited) };
  }

  // Anonymous pure callable type `(a: T, b: U) => R` (no properties, not a named
  // interface). Named callable interfaces (`interface Fix { (x: Fix): void }`)
  // fall through to the symbol branch so their identity is preserved and self-
  // referential signatures cannot overflow the stack.
  const callSigs = type.getCallSignatures();
  if (!type.isInterface() && callSigs.length > 0 && type.getProperties().length === 0) {
    if (visited.has(type)) return { kind: "unknown" };
    const nextVisited = new Set(visited);
    nextVisited.add(type);
    const sig = callSigs[0];
    const params = sig.getParameters().map(p => {
      const decl = p.getValueDeclaration();
      const pt = decl ? p.getTypeAtLocation(decl) : p.getDeclaredType();
      return lowerCheckerType(pt, ctx, nextVisited);
    });
    const result = lowerCheckerType(sig.getReturnType(), ctx, nextVisited);
    return { kind: "fn", params, result };
  }

  const symbol = type.getSymbol();

  if (symbol) {
    const name = symbol.getName();
    // Recover collapsed single-variant union alias via property fingerprint.
    if (name === "__type" && ctx.collapsedUnionMap && ctx.collapsedUnionMap.size > 0) {
      const props = type.getProperties().map(p => p.getName()).sort().join(",");
      const alias = ctx.collapsedUnionMap.get(props);
      if (alias) return { kind: "user", name: alias };
    }
    const typeArgs = type.getTypeArguments();
    if (typeArgs.length > 0) {
      if (visited.has(type)) return { kind: "user", name };
      const nextVisited = new Set(visited);
      nextVisited.add(type);
      const loweredArgs = typeArgs.map(t => lowerCheckerType(t, ctx, nextVisited));
      const builtin = lowerBuiltinCollection(name, loweredArgs);
      if (builtin) return builtin;
      return { kind: "user", name: `${name}<${typeArgs.map(t => typeToTsString(t, ctx)).join(", ")}>` };
    }
    return { kind: "user", name };
  }

  const text = type.getText();
  if (text === "void" || text === "undefined") return { kind: "void" };
  if (text === "null") return { kind: "null" };
  if (text === "any" || text === "unknown") return { kind: "unknown" };
  return { kind: "user", name: text };
}
