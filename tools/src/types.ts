/**
 * Type mapping — TS type strings → backend-neutral `Ty`.
 *
 * Single source of truth for type-related decisions; resolve, transform, and
 * both emitters import this.
 */

// ── Type info extracted from TS ──────────────────────────────

export interface FieldInfo {
  name: string;
  tsType: string;
  type?: Ty;     // pre-computed Ty — populated by resolveModule, avoids re-parsing tsType
  /** Declared with `?` (`f?: T`): the key itself may be absent, not just the value. */
  optionalKey?: boolean;
}

export interface VariantInfo {
  name: string;
  fields: FieldInfo[];
}

export interface UnionTypeInfo {
  name: string;
  discriminant: string;
  variants: VariantInfo[];
}

export interface TypeDeclInfo {
  name: string;
  typeParams?: string[];
  kind: "string-union" | "discriminated-union" | "record" | "alias" | "opaque";
  /** For string unions: the literal values */
  values?: string[];
  /** For discriminated unions: the discriminant field and variants */
  discriminant?: string;
  variants?: VariantInfo[];
  /** For records: the fields */
  fields?: FieldInfo[];
  /** For alias: the underlying type string */
  aliasOf?: string;
  aliasOfTy?: Ty;  // pre-computed Ty for aliasOf
  /** Numeric const enum: integer semantics; members exist only on value bindings.
   * A type-only alias has an empty member list. */
  constEnumMembers?: { name: string; value: number }[];
}

// ── TS type string → Ty (single source of truth) ───────────

import type { Ty } from "./typedir.js";
import { tyEqual } from "./typedir.js";
import { optional } from "./nullish.js";
import { Node, Project, SyntaxKind } from "ts-morph";
import type { Project as TsProject, SourceFile, TypeNode } from "ts-morph";

/**
 * Parses TS type strings via a real ts-morph parse — no regex cascade. Set
 * once per run by `extractModule` (so it reuses the module's Project); a
 * separate in-memory Project is created lazily for callers that hit
 * `parseTsType` outside the extract pipeline (e.g. tests, `lsc info` when
 * driven independently).
 */
let _synthFile: SourceFile | null = null;

export function initTypeParser(project: TsProject): void {
  _synthFile = project.createSourceFile("__lsc_type_parse__.ts", "", { overwrite: true });
}

function synthFile(): SourceFile {
  if (_synthFile) return _synthFile;
  const p = new Project({ useInMemoryFileSystem: true });
  _synthFile = p.createSourceFile("__lsc_type_parse__.ts", "");
  return _synthFile;
}

export function parseTsType(tsType: string): Ty {
  const sf = synthFile();
  sf.replaceWithText(`type __t = ${tsType};`);
  const alias = sf.getTypeAliasOrThrow("__t");
  return tyFromTypeNode(alias.getTypeNodeOrThrow());
}

function tyFromTypeNode(tn: TypeNode): Ty {
  if (Node.isParenthesizedTypeNode(tn)) return tyFromTypeNode(tn.getTypeNode());
  // `readonly T[]` / `readonly [A, B]` — the modifier is a TypeOperator wrapping
  // the array/tuple; verification treats it identically to the mutable form.
  if (Node.isTypeOperatorTypeNode(tn) && tn.getOperator() === SyntaxKind.ReadonlyKeyword) {
    return tyFromTypeNode(tn.getTypeNode());
  }
  if (Node.isUnionTypeNode(tn)) {
    const unionArms = (node: TypeNode): TypeNode[] => Node.isParenthesizedTypeNode(node)
      ? unionArms(node.getTypeNode())
      : Node.isUnionTypeNode(node) ? node.getTypeNodes().flatMap(unionArms) : [node];
    const arms = tn.getTypeNodes().flatMap(unionArms);
    const isBoolLit = (a: TypeNode) =>
      Node.isLiteralTypeNode(a) && (a.getLiteral().getKind() === SyntaxKind.TrueKeyword || a.getLiteral().getKind() === SyntaxKind.FalseKeyword);
    const isNullish = (a: TypeNode) =>
      a.getKind() === SyntaxKind.NullKeyword ||
      a.getKind() === SyntaxKind.UndefinedKeyword ||
      (Node.isLiteralTypeNode(a) && a.getLiteral().getKind() === SyntaxKind.NullKeyword);
    // Collapse expanded boolean (`true | false`) into a single bool slot, so
    // `boolean | undefined` (which TS expands to `false | true | undefined`)
    // still reads as `optional<bool>` rather than falling through to user.
    const hasTrueLit = arms.some(a => Node.isLiteralTypeNode(a) && a.getLiteral().getKind() === SyntaxKind.TrueKeyword);
    const hasFalseLit = arms.some(a => Node.isLiteralTypeNode(a) && a.getLiteral().getKind() === SyntaxKind.FalseKeyword);
    const collapseBool = hasTrueLit && hasFalseLit;
    const normalized: ({ node: TypeNode } | { syntheticBool: true })[] =
      collapseBool
        ? [{ syntheticBool: true } as const, ...arms.filter(a => !isBoolLit(a)).map(node => ({ node }))]
        : arms.map(node => ({ node }));
    if (normalized.length === 1 && "syntheticBool" in normalized[0]) return { kind: "bool" };
    const nonNullish = normalized.filter(a => "syntheticBool" in a || !isNullish(a.node));
    const hasNull = arms.some(a => isNullish(a) && a.getText() === "null");
    const hasUndefined = arms.some(a => a.getKind() === SyntaxKind.UndefinedKeyword);
    const nullish = hasNull && hasUndefined ? "both" : hasNull ? "null" : "undefined";
    if (nonNullish.length === 0) return { kind: "nullish", nullish };
    // Inline string-literal union (`"a" | "b"`, not a //@ declare-type): no datatype
    // to resolve against, so lower to plain string (the arms are strings; == holds).
    const isStrLit = (a: { node: TypeNode } | { syntheticBool: true }) =>
      !("syntheticBool" in a) && Node.isLiteralTypeNode(a.node) && a.node.getLiteral().getKind() === SyntaxKind.StringLiteral;
    if (nonNullish.length >= 2 && nonNullish.every(isStrLit)) {
      // Keep the literal members so `rec[k]` can lower to an equality chain.
      const values = nonNullish.map(a => {
        const lit = (a as { node: TypeNode }).node;
        const inner = Node.isLiteralTypeNode(lit) ? lit.getLiteral() : lit;
        return Node.isStringLiteral(inner) ? inner.getLiteralValue() : inner.getText();
      });
      return normalized.some(a => !("syntheticBool" in a) && isNullish(a.node))
        ? optional({ kind: "string", values }, nullish)
        : { kind: "string", values };
    }
    // Numeric literal unions have the same integer model as number, including
    // in inline annotations and optional types with several numeric arms.
    if (nonNullish.length >= 2 && nonNullish.every(a => {
      if ("syntheticBool" in a) return false;
      const ty = tyFromTypeNode(a.node);
      return ty.kind === "int" && !ty.big;
    })) {
      const inner: Ty = { kind: "int" };
      return normalized.some(a => !("syntheticBool" in a) && isNullish(a.node))
        ? optional(inner, nullish) : inner;
    }
    if (nonNullish.length === 1 && normalized.length >= 2) {
      const sole = nonNullish[0];
      const inner: Ty = "syntheticBool" in sole ? { kind: "bool" } : tyFromTypeNode(sole.node);
      return optional(inner, nullish);
    }
    // Multi-member union with a nullish arm (`A | B | undefined`): the
    // structured part is opaque to us, but the optionality isn't. Expose it as
    // optional<user "A | B"> so downstream (e.g. the let-type merge in resolve)
    // can keep the nullability while taking structure from a more precise
    // source. Without this the whole thing collapses to one opaque user blob.
    const hadNullish = normalized.some(a => !("syntheticBool" in a) && isNullish(a.node));
    if (hadNullish && nonNullish.length >= 2) {
      const innerName = nonNullish.map(a => ("syntheticBool" in a ? "boolean" : a.node.getText())).join(" | ");
      return optional({ kind: "user", name: innerName }, nullish);
    }
    // Other unions: leave as a user type spelled how the source wrote it.
    return { kind: "user", name: tn.getText() };
  }
  if (Node.isArrayTypeNode(tn)) return { kind: "array", elem: tyFromTypeNode(tn.getElementTypeNode()) };
  if (Node.isTupleTypeNode(tn)) {
    const elems = tn.getElements().map(tyFromTypeNode);
    if (elems.length === 0) return { kind: "array", elem: { kind: "unknown" } };
    // Homogeneous tuple → seq; only heterogeneous tuples need the tuple
    // representation.
    if (elems.every(e => tyEqual(e, elems[0]))) return { kind: "array", elem: elems[0] };
    return { kind: "tuple", elems };
  }
  if (Node.isFunctionTypeNode(tn)) {
    const params = tn.getParameters().map(p => {
      const ptn = p.getTypeNode();
      return ptn ? tyFromTypeNode(ptn) : { kind: "unknown" as const };
    });
    const result = tyFromTypeNode(tn.getReturnTypeNodeOrThrow());
    return { kind: "fn", params, result };
  }
  if (Node.isLiteralTypeNode(tn)) {
    const literal = tn.getLiteral();
    const lk = literal.getKind();
    if (lk === SyntaxKind.NullKeyword) return { kind: "nullish", nullish: "null" };
    if (lk === SyntaxKind.TrueKeyword || lk === SyntaxKind.FalseKeyword) return { kind: "bool" };
    if (Node.isNumericLiteral(literal) ||
        (Node.isPrefixUnaryExpression(literal) && Node.isNumericLiteral(literal.getOperand()))) return { kind: "int" };
  }
  switch (tn.getKind()) {
    case SyntaxKind.NumberKeyword:
      return { kind: "int" };
    case SyntaxKind.BigIntKeyword:
      return { kind: "int", big: true };
    case SyntaxKind.BooleanKeyword:
      return { kind: "bool" };
    case SyntaxKind.StringKeyword:
      return { kind: "string" };
    case SyntaxKind.VoidKeyword:
      return { kind: "void" };
    case SyntaxKind.UndefinedKeyword:
      return { kind: "nullish", nullish: "undefined" };
    case SyntaxKind.UnknownKeyword:
    case SyntaxKind.AnyKeyword:
      return { kind: "unknown" };
  }
  if (Node.isTypeReference(tn)) {
    const name = tn.getTypeName().getText();
    const args = tn.getTypeArguments();
    if (name === "nat" && args.length === 0) return { kind: "nat" };
    if (name === "real" && args.length === 0) return { kind: "real" };
    if (name === "int" && args.length === 0) return { kind: "int" };
    if ((name === "Array" || name === "ReadonlyArray") && args.length === 1) return { kind: "array", elem: tyFromTypeNode(args[0]) };
    if ((name === "Set" || name === "ReadonlySet") && args.length === 1) return { kind: "set", elem: tyFromTypeNode(args[0]) };
    if ((name === "Map" || name === "ReadonlyMap" || name === "Record") && args.length === 2) {
      return { kind: "map", key: tyFromTypeNode(args[0]), value: tyFromTypeNode(args[1]) };
    }
    // User-named type: include generic args in the spelled name so callers
    // that key on the string (e.g. typedir alias lookups) see the exact form.
    return { kind: "user", name: tn.getText() };
  }
  return { kind: "user", name: tn.getText() };
}

/** Render a Ty in LemmaScript canonical syntax — backend-neutral, side-effect-free.
 *  Used by `lsc info` for the signature field of `foo.ts.json`. */
export function tyToCanonical(ty: Ty): string {
  switch (ty.kind) {
    case "bool":   return "bool";
    case "nat":    return "nat";
    case "int":    return "int";
    case "real":   return "real";
    case "string": return "string";
    case "void":   return "void";
    case "nullish": return ty.nullish === "both" ? "null | undefined" : ty.nullish;
    case "unknown":return "unknown";
    case "array":  return `seq<${tyToCanonical(ty.elem)}>`;
    case "tuple":  return `(${ty.elems.map(tyToCanonical).join(", ")})`;
    case "map":    return `map<${tyToCanonical(ty.key)}, ${tyToCanonical(ty.value)}>`;
    case "set":    return `set<${tyToCanonical(ty.elem)}>`;
    case "optional": return `Option<${tyToCanonical(ty.inner)}, ${ty.nullish}>`;
    case "user":   return ty.name;
    case "fn":     return `(${ty.params.map(tyToCanonical).join(", ")}) -> ${tyToCanonical(ty.result)}`;
  }
}

