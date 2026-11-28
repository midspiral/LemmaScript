//@ backend dafny
/**
 * Self-verified parser for LemmaScript `//@` spec-annotation type expressions.
 *
 * Pure, zero `ts-morph` imports. Verified by LemmaScript itself (Dafny backend):
 * - Tokenizer termination and cursor progress on every character.
 * - Recursive-descent parser termination and strict cursor progress on every
 *   accepted parse (`pos < nextPos <= tokens.length`).
 * - Full-input consumption (`DESIGN_LS_IN_LS.md` §8.4 property #7): every
 *   accepted parse consumes the entire token stream (`nextPos === tokens.length`).
 * - Fail-closed error results on empty, malformed, unsupported, or trailing-token
 *   inputs.
 */

export type SpecTokenKind =
  | "ident"
  | "number"
  | "str"
  | "arrow"
  | "lt"
  | "gt"
  | "lbracket"
  | "rbracket"
  | "lparen"
  | "rparen"
  | "comma"
  | "pipe"
  | "colon"
  | "dot"
  | "minus"
  | "question";

export interface SpecTypeToken {
  kind: SpecTokenKind;
  text: string;
  /** Unescaped string value for `"str"` tokens; empty for other kinds. */
  strVal: string;
}

export type TokenizeResult =
  | { kind: "ok"; tokens: SpecTypeToken[] }
  | { kind: "err"; error: string };

export type SpecTy =
  | { kind: "bool" }
  | { kind: "nat" }
  | { kind: "int" }
  | { kind: "bigint" }
  | { kind: "real" }
  | { kind: "string" }
  | { kind: "stringUnion"; values: string[] }
  | { kind: "void" }
  | { kind: "null" }
  | { kind: "array"; elem: SpecTy }
  | { kind: "tuple"; elems: SpecTy[] }
  | { kind: "map"; key: SpecTy; value: SpecTy }
  | { kind: "set"; elem: SpecTy }
  | { kind: "optionalUndef"; inner: SpecTy }
  | { kind: "optionalNull"; inner: SpecTy }
  | { kind: "nullish"; inner: SpecTy }
  | { kind: "user"; name: string }
  | { kind: "fn"; params: SpecTy[]; result: SpecTy }
  | { kind: "unknown" };

export type SpecParseResult =
  | { kind: "ok"; ty: SpecTy; raw: string; nextPos: number }
  | { kind: "err"; error: string };

interface UnionArm {
  ty: SpecTy;
  raw: string;
  isBoolTrue: boolean;
  isBoolFalse: boolean;
  isNullLit: boolean;
  isUndefLit: boolean;
  isStrLit: boolean;
  strLitVal: string;
}

// ── Character classification ─────────────────────────────────

function isWhitespaceCode(c: number): boolean {
  return c === 32 || c === 9 || c === 10 || c === 13;
}

function isDigitCode(c: number): boolean {
  return c >= 48 && c <= 57;
}

function isIdentStartCode(c: number): boolean {
  return (c >= 65 && c <= 90)
    || (c >= 97 && c <= 122)
    || c === 95
    || c === 36;
}

function isIdentPartCode(c: number): boolean {
  return isIdentStartCode(c) || isDigitCode(c);
}

// ── Tokenizer ────────────────────────────────────────────────

export function tokenizeSpecType(input: string): TokenizeResult {
  const tokens: SpecTypeToken[] = [];
  let i = 0;
  while (i < input.length) {
    //@ invariant 0 <= i && i <= input.length
    //@ decreases input.length - i
    const c = input.charCodeAt(i);
    if (isWhitespaceCode(c)) {
      i = i + 1;
      continue;
    }
    if (isIdentStartCode(c)) {
      const start = i;
      i = i + 1;
      while (i < input.length && isIdentPartCode(input.charCodeAt(i))) {
        //@ invariant start < i && i <= input.length
        //@ decreases input.length - i
        i = i + 1;
      }
      tokens.push({ kind: "ident", text: input.slice(start, i), strVal: "" });
      continue;
    }
    if (isDigitCode(c)) {
      const start = i;
      i = i + 1;
      while (i < input.length && isDigitCode(input.charCodeAt(i))) {
        //@ invariant start < i && i <= input.length
        //@ decreases input.length - i
        i = i + 1;
      }
      tokens.push({ kind: "number", text: input.slice(start, i), strVal: "" });
      continue;
    }
    if (c === 34 || c === 39) {
      // Quoted string literal ("..." or '...')
      const quote = c;
      const start = i;
      i = i + 1;
      let val = "";
      let closed = false;
      while (i < input.length) {
        //@ invariant start < i && i <= input.length
        //@ decreases input.length - i
        const ch = input.charCodeAt(i);
        if (ch === 92) {
          // Backslash escape
          if (i + 1 >= input.length) {
            return { kind: "err", error: "Unterminated escape in string literal type" };
          }
          const escCode = input.charCodeAt(i + 1);
          if (escCode === 110) {
            val = val + "\n";
          } else if (escCode === 114) {
            val = val + "\r";
          } else if (escCode === 116) {
            val = val + "\t";
          } else {
            val = val + input.slice(i + 1, i + 2);
          }
          i = i + 2;
        } else if (ch === quote) {
          i = i + 1;
          closed = true;
          break;
        } else {
          val = val + input.slice(i, i + 1);
          i = i + 1;
        }
      }
      if (!closed) {
        return { kind: "err", error: "Unterminated string literal type" };
      }
      tokens.push({ kind: "str", text: input.slice(start, i), strVal: val });
      continue;
    }
    if (c === 61) {
      // '=' must be part of '=>'
      if (i + 1 < input.length && input.charCodeAt(i + 1) === 62) {
        tokens.push({ kind: "arrow", text: "=>", strVal: "" });
        i = i + 2;
        continue;
      }
      return { kind: "err", error: "Unexpected '=' in type annotation (expected '=>')" };
    }
    if (c === 60) { tokens.push({ kind: "lt", text: "<", strVal: "" }); i = i + 1; continue; }
    if (c === 62) { tokens.push({ kind: "gt", text: ">", strVal: "" }); i = i + 1; continue; }
    if (c === 91) { tokens.push({ kind: "lbracket", text: "[", strVal: "" }); i = i + 1; continue; }
    if (c === 93) { tokens.push({ kind: "rbracket", text: "]", strVal: "" }); i = i + 1; continue; }
    if (c === 40) { tokens.push({ kind: "lparen", text: "(", strVal: "" }); i = i + 1; continue; }
    if (c === 41) { tokens.push({ kind: "rparen", text: ")", strVal: "" }); i = i + 1; continue; }
    if (c === 44) { tokens.push({ kind: "comma", text: ",", strVal: "" }); i = i + 1; continue; }
    if (c === 124) { tokens.push({ kind: "pipe", text: "|", strVal: "" }); i = i + 1; continue; }
    if (c === 58) { tokens.push({ kind: "colon", text: ":", strVal: "" }); i = i + 1; continue; }
    if (c === 46) { tokens.push({ kind: "dot", text: ".", strVal: "" }); i = i + 1; continue; }
    if (c === 45) { tokens.push({ kind: "minus", text: "-", strVal: "" }); i = i + 1; continue; }
    if (c === 63) { tokens.push({ kind: "question", text: "?", strVal: "" }); i = i + 1; continue; }
    return { kind: "err", error: "Unexpected character '" + input.slice(i, i + 1) + "' in type annotation" };
  }
  return { kind: "ok", tokens };
}

// ── Structural helpers ───────────────────────────────────────

function stringSeqEqual(a: string[], b: string[]): boolean {
  if (a.length !== b.length) return false;
  let i = 0;
  while (i < a.length) {
    //@ invariant 0 <= i && i <= a.length
    //@ decreases a.length - i
    if (a[i] !== b[i]) return false;
    i = i + 1;
  }
  return true;
}

export function specTyEqual(a: SpecTy, b: SpecTy): boolean {
  //@ decreases a
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "bool":
    case "nat":
    case "int":
    case "bigint":
    case "real":
    case "string":
    case "void":
    case "null":
    case "unknown":
      return true;
    case "stringUnion":
      return b.kind === "stringUnion" && stringSeqEqual(a.values, b.values);
    case "user":
      return b.kind === "user" && a.name === b.name;
    case "array":
      return b.kind === "array" && specTyEqual(a.elem, b.elem);
    case "set":
      return b.kind === "set" && specTyEqual(a.elem, b.elem);
    case "optionalUndef":
      return b.kind === "optionalUndef" && specTyEqual(a.inner, b.inner);
    case "optionalNull":
      return b.kind === "optionalNull" && specTyEqual(a.inner, b.inner);
    case "nullish":
      return b.kind === "nullish" && specTyEqual(a.inner, b.inner);
    case "map":
      return b.kind === "map" && specTyEqual(a.key, b.key) && specTyEqual(a.value, b.value);
    case "tuple":
      return b.kind === "tuple" && specTyListEqual(a.elems, b.elems);
    case "fn":
      return b.kind === "fn" && specTyListEqual(a.params, b.params) && specTyEqual(a.result, b.result);
  }
}

function specTyListEqual(a: SpecTy[], b: SpecTy[]): boolean {
  //@ decreases a
  if (a.length !== b.length) return false;
  let i = 0;
  while (i < a.length) {
    //@ invariant 0 <= i && i <= a.length
    //@ decreases a.length - i
    if (!specTyEqual(a[i], b[i])) return false;
    i = i + 1;
  }
  return true;
}

export function isOptionalSpecTy(t: SpecTy): boolean {
  return t.kind === "optionalUndef" || t.kind === "optionalNull" || t.kind === "nullish";
}

export function wrapNullability(inner: SpecTy, hasNull: boolean, hasUndef: boolean): SpecTy {
  //@ ensures \result.kind === "optionalUndef" ==> !isOptionalSpecTy(\result.inner) && \result.inner.kind !== "null" && \result.inner.kind !== "void"
  //@ ensures \result.kind === "optionalNull" ==> !isOptionalSpecTy(\result.inner) && \result.inner.kind !== "null" && \result.inner.kind !== "void"
  //@ ensures \result.kind === "nullish" ==> !isOptionalSpecTy(\result.inner)
  //@ ensures (!hasNull && !hasUndef && !isOptionalSpecTy(inner)) ==> \result === inner
  //@ ensures (hasNull && hasUndef) ==> \result.kind === "nullish"
  let payload: SpecTy = inner;
  let mergedNull = hasNull;
  let mergedUndef = hasUndef;
  while (payload.kind === "optionalUndef" || payload.kind === "optionalNull" || payload.kind === "nullish") {
    //@ invariant hasNull ==> mergedNull
    //@ invariant hasUndef ==> mergedUndef
    //@ invariant (!isOptionalSpecTy(inner)) ==> (payload === inner && mergedNull === hasNull && mergedUndef === hasUndef)
    //@ decreases payload
    if (payload.kind === "nullish") {
      mergedNull = true;
      mergedUndef = true;
      payload = payload.inner;
    } else if (payload.kind === "optionalNull") {
      mergedNull = true;
      payload = payload.inner;
    } else {
      mergedUndef = true;
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
  if (mergedNull) return { kind: "optionalNull", inner: payload };
  if (mergedUndef) return { kind: "optionalUndef", inner: payload };
  return payload;
}

function joinWith(parts: string[], sep: string): string {
  if (parts.length === 0) return "";
  let out = parts[0];
  let i = 1;
  while (i < parts.length) {
    //@ invariant 1 <= i && i <= parts.length
    //@ decreases parts.length - i
    out = out + sep + parts[i];
    i = i + 1;
  }
  return out;
}

// ── Lookahead for function types ─────────────────────────────

/** True when `tokens[pos]` is `(` whose matching `)` is immediately followed by `=>`. */
function isFunctionTypeStart(tokens: SpecTypeToken[], pos: number): boolean {
  //@ requires 0 <= pos && pos <= tokens.length
  //@ ensures \result ==> pos < tokens.length && tokens[pos].kind === "lparen"
  if (pos >= tokens.length || tokens[pos].kind !== "lparen") return false;
  let depth = 1;
  let i = pos + 1;
  while (i < tokens.length) {
    //@ invariant pos < i && i <= tokens.length
    //@ invariant depth >= 1
    //@ decreases tokens.length - i
    const k = tokens[i].kind;
    if (k === "lparen") {
      depth = depth + 1;
    } else if (k === "rparen") {
      depth = depth - 1;
      if (depth === 0) {
        return i + 1 < tokens.length && tokens[i + 1].kind === "arrow";
      }
    }
    i = i + 1;
  }
  return false;
}

// ── Recursive-descent parser ─────────────────────────────────

function parseType(tokens: SpecTypeToken[], pos: number): SpecParseResult {
  //@ requires 0 <= pos && pos <= tokens.length
  //@ ensures \result.kind === "ok" ==> pos < \result.nextPos && \result.nextPos <= tokens.length
  //@ decreases (tokens.length - pos) * 10 + 5
  if (pos >= tokens.length) {
    return { kind: "err", error: "Unexpected end of type annotation" };
  }
  if (isFunctionTypeStart(tokens, pos)) {
    return parseFnType(tokens, pos);
  }
  return parseUnion(tokens, pos);
}

function parseFnType(tokens: SpecTypeToken[], pos: number): SpecParseResult {
  //@ requires 0 <= pos && pos < tokens.length
  //@ requires tokens[pos].kind === "lparen"
  //@ ensures \result.kind === "ok" ==> pos < \result.nextPos && \result.nextPos <= tokens.length
  //@ decreases (tokens.length - pos) * 10 + 4
  let cur = pos + 1;
  const params: SpecTy[] = [];
  const paramRaws: string[] = [];
  if (cur < tokens.length && tokens[cur].kind !== "rparen") {
    while (true) {
      //@ invariant pos < cur && cur <= tokens.length
      //@ decreases tokens.length - cur
      if (cur >= tokens.length) {
        return { kind: "err", error: "Unterminated parameter list in function type" };
      }
      if (tokens[cur].kind !== "ident") {
        return { kind: "err", error: "Expected parameter name in function type" };
      }
      const pName = tokens[cur].text;
      cur = cur + 1;
      let optMark = "";
      if (cur < tokens.length && tokens[cur].kind === "question") {
        optMark = "?";
        cur = cur + 1;
      }
      let pTy: SpecTy = { kind: "unknown" };
      let pRaw = pName + optMark;
      if (cur < tokens.length && tokens[cur].kind === "colon") {
        cur = cur + 1;
        const tRes = parseType(tokens, cur);
        if (tRes.kind === "err") return tRes;
        pTy = optMark === "?" ? wrapNullability(tRes.ty, false, true) : tRes.ty;
        pRaw = pName + optMark + ": " + tRes.raw;
        cur = tRes.nextPos;
      } else if (optMark === "?") {
        pTy = wrapNullability(pTy, false, true);
      }
      params.push(pTy);
      paramRaws.push(pRaw);
      if (cur < tokens.length && tokens[cur].kind === "comma") {
        cur = cur + 1;
        if (cur < tokens.length && tokens[cur].kind === "rparen") {
          break;
        }
        continue;
      }
      break;
    }
  }
  if (cur >= tokens.length || tokens[cur].kind !== "rparen") {
    return { kind: "err", error: "Expected ')' in function type" };
  }
  cur = cur + 1;
  if (cur >= tokens.length || tokens[cur].kind !== "arrow") {
    return { kind: "err", error: "Expected '=>' in function type" };
  }
  cur = cur + 1;
  const retRes = parseType(tokens, cur);
  if (retRes.kind === "err") return retRes;
  const raw = "(" + joinWith(paramRaws, ", ") + ") => " + retRes.raw;
  return { kind: "ok", ty: { kind: "fn", params, result: retRes.ty }, raw, nextPos: retRes.nextPos };
}

function makeUnionArm(tokens: SpecTypeToken[], armStart: number, armEnd: number, ty: SpecTy, raw: string): UnionArm {
  //@ requires 0 <= armStart && armStart < armEnd && armEnd <= tokens.length
  const single = armEnd === armStart + 1;
  const tok = tokens[armStart];
  const isBoolTrue = single && tok.kind === "ident" && tok.text === "true";
  const isBoolFalse = single && tok.kind === "ident" && tok.text === "false";
  const isNullLit = single && tok.kind === "ident" && tok.text === "null";
  const isUndefLit = single && tok.kind === "ident" && tok.text === "undefined";
  const isStrLit = single && tok.kind === "str";
  const strLitVal = isStrLit ? tok.strVal : "";
  return { ty, raw, isBoolTrue, isBoolFalse, isNullLit, isUndefLit, isStrLit, strLitVal };
}

function resolveUnionArms(arms: UnionArm[]): SpecTy {
  //@ requires arms.length >= 1
  if (arms.length === 1) {
    return arms[0].ty;
  }
  let hasNull = false;
  let hasUndef = false;
  let hasTrue = false;
  let hasFalse = false;
  let i = 0;
  while (i < arms.length) {
    //@ invariant 0 <= i && i <= arms.length
    //@ decreases arms.length - i
    if (arms[i].isNullLit) hasNull = true;
    if (arms[i].isUndefLit) hasUndef = true;
    if (arms[i].isBoolTrue) hasTrue = true;
    if (arms[i].isBoolFalse) hasFalse = true;
    i = i + 1;
  }
  const collapseBool = hasTrue && hasFalse;
  const normalized: UnionArm[] = [];
  if (collapseBool) {
    normalized.push({
      ty: { kind: "bool" },
      raw: "boolean",
      isBoolTrue: false,
      isBoolFalse: false,
      isNullLit: false,
      isUndefLit: false,
      isStrLit: false,
      strLitVal: "",
    });
  }
  i = 0;
  while (i < arms.length) {
    //@ invariant 0 <= i && i <= arms.length
    //@ decreases arms.length - i
    const a = arms[i];
    if (!(collapseBool && (a.isBoolTrue || a.isBoolFalse))) {
      normalized.push(a);
    }
    i = i + 1;
  }
  if (normalized.length === 1 && collapseBool) {
    return { kind: "bool" };
  }
  const nonNullish: UnionArm[] = [];
  i = 0;
  while (i < normalized.length) {
    //@ invariant 0 <= i && i <= normalized.length
    //@ decreases normalized.length - i
    const a = normalized[i];
    if (!a.isNullLit && !a.isUndefLit) {
      nonNullish.push(a);
    }
    i = i + 1;
  }
  if (nonNullish.length === 0) {
    if (hasNull && hasUndef) return { kind: "nullish", inner: { kind: "void" } };
    if (hasNull) return { kind: "null" };
    return { kind: "void" };
  }
  if (nonNullish.length === 1) {
    return wrapNullability(nonNullish[0].ty, hasNull, hasUndef);
  }
  // Check if all non-nullish arms are string literals
  let allStr = true;
  const strVals: string[] = [];
  i = 0;
  while (i < nonNullish.length) {
    //@ invariant 0 <= i && i <= nonNullish.length
    //@ decreases nonNullish.length - i
    if (!nonNullish[i].isStrLit) {
      allStr = false;
    } else {
      strVals.push(nonNullish[i].strLitVal);
    }
    i = i + 1;
  }
  if (allStr) {
    return wrapNullability({ kind: "stringUnion", values: strVals }, hasNull, hasUndef);
  }
  // Check if all non-nullish arms are non-bigint int
  let allInt = true;
  i = 0;
  while (i < nonNullish.length) {
    //@ invariant 0 <= i && i <= nonNullish.length
    //@ decreases nonNullish.length - i
    if (nonNullish[i].ty.kind !== "int") {
      allInt = false;
    }
    i = i + 1;
  }
  if (allInt) {
    return wrapNullability({ kind: "int" }, hasNull, hasUndef);
  }
  if (hasNull || hasUndef) {
    const innerRaws: string[] = [];
    i = 0;
    while (i < nonNullish.length) {
      //@ invariant 0 <= i && i <= nonNullish.length
      //@ decreases nonNullish.length - i
      innerRaws.push(nonNullish[i].raw);
      i = i + 1;
    }
    return wrapNullability({ kind: "user", name: joinWith(innerRaws, " | ") }, hasNull, hasUndef);
  }
  const allRaws: string[] = [];
  i = 0;
  while (i < arms.length) {
    //@ invariant 0 <= i && i <= arms.length
    //@ decreases arms.length - i
    allRaws.push(arms[i].raw);
    i = i + 1;
  }
  return { kind: "user", name: joinWith(allRaws, " | ") };
}

function parseUnion(tokens: SpecTypeToken[], pos: number): SpecParseResult {
  //@ requires 0 <= pos && pos < tokens.length
  //@ ensures \result.kind === "ok" ==> pos < \result.nextPos && \result.nextPos <= tokens.length
  //@ decreases (tokens.length - pos) * 10 + 3
  let cur = pos;
  // Allow leading `|` (standard TS syntax: `| A | B`)
  if (tokens[cur].kind === "pipe") {
    cur = cur + 1;
    if (cur >= tokens.length) {
      return { kind: "err", error: "Expected type after leading '|'" };
    }
  }
  const firstStart = cur;
  const first = parsePostfix(tokens, cur);
  if (first.kind === "err") return first;
  const arms: UnionArm[] = [makeUnionArm(tokens, firstStart, first.nextPos, first.ty, first.raw)];
  const raws: string[] = [first.raw];
  cur = first.nextPos;
  while (cur < tokens.length && tokens[cur].kind === "pipe") {
    //@ invariant pos < cur && cur <= tokens.length
    //@ invariant arms.length >= 1
    //@ decreases tokens.length - cur
    cur = cur + 1;
    if (cur >= tokens.length) {
      return { kind: "err", error: "Expected type after '|'" };
    }
    const armStart = cur;
    const arm = parsePostfix(tokens, cur);
    if (arm.kind === "err") return arm;
    arms.push(makeUnionArm(tokens, armStart, arm.nextPos, arm.ty, arm.raw));
    raws.push(arm.raw);
    cur = arm.nextPos;
  }
  const ty = resolveUnionArms(arms);
  return { kind: "ok", ty, raw: joinWith(raws, " | "), nextPos: cur };
}

function parsePostfix(tokens: SpecTypeToken[], pos: number): SpecParseResult {
  //@ requires 0 <= pos && pos < tokens.length
  //@ ensures \result.kind === "ok" ==> pos < \result.nextPos && \result.nextPos <= tokens.length
  //@ decreases (tokens.length - pos) * 10 + 2
  if (tokens[pos].kind === "ident" && tokens[pos].text === "readonly") {
    if (pos + 1 >= tokens.length) {
      return { kind: "err", error: "Expected type after 'readonly'" };
    }
    const inner = parsePostfix(tokens, pos + 1);
    if (inner.kind === "err") return inner;
    return { kind: "ok", ty: inner.ty, raw: "readonly " + inner.raw, nextPos: inner.nextPos };
  }
  const base = parsePrimary(tokens, pos);
  if (base.kind === "err") return base;
  let ty = base.ty;
  let raw = base.raw;
  let cur = base.nextPos;
  while (cur + 1 < tokens.length && tokens[cur].kind === "lbracket" && tokens[cur + 1].kind === "rbracket") {
    //@ invariant pos < cur && cur <= tokens.length
    //@ decreases tokens.length - cur
    ty = { kind: "array", elem: ty };
    raw = raw + "[]";
    cur = cur + 2;
  }
  return { kind: "ok", ty, raw, nextPos: cur };
}

function parsePrimary(tokens: SpecTypeToken[], pos: number): SpecParseResult {
  //@ requires 0 <= pos && pos < tokens.length
  //@ ensures \result.kind === "ok" ==> pos < \result.nextPos && \result.nextPos <= tokens.length
  //@ decreases (tokens.length - pos) * 10 + 1
  const tok = tokens[pos];

  // Parenthesized type: (T)
  if (tok.kind === "lparen") {
    const inner = parseType(tokens, pos + 1);
    if (inner.kind === "err") return inner;
    if (inner.nextPos >= tokens.length || tokens[inner.nextPos].kind !== "rparen") {
      return { kind: "err", error: "Expected ')' after parenthesized type" };
    }
    return { kind: "ok", ty: inner.ty, raw: "(" + inner.raw + ")", nextPos: inner.nextPos + 1 };
  }

  // Tuple type: [T1, T2, ...]
  if (tok.kind === "lbracket") {
    let cur = pos + 1;
    const elems: SpecTy[] = [];
    const elemRaws: string[] = [];
    if (cur < tokens.length && tokens[cur].kind !== "rbracket") {
      while (true) {
        //@ invariant pos < cur && cur <= tokens.length
        //@ decreases tokens.length - cur
        if (cur >= tokens.length) {
          return { kind: "err", error: "Unterminated tuple type" };
        }
        // Optional named tuple label: `label: T` or `label?: T`
        let isOptionalElem = false;
        if (tokens[cur].kind === "ident" && cur + 1 < tokens.length) {
          if (tokens[cur + 1].kind === "colon") {
            cur = cur + 2;
          } else if (tokens[cur + 1].kind === "question" && cur + 2 < tokens.length && tokens[cur + 2].kind === "colon") {
            isOptionalElem = true;
            cur = cur + 3;
          }
        }
        const elemRes = parseType(tokens, cur);
        if (elemRes.kind === "err") return elemRes;
        let elemTy = elemRes.ty;
        let elemRaw = elemRes.raw;
        cur = elemRes.nextPos;
        // Unnamed optional tuple element: `[number, string?]`
        if (cur < tokens.length && tokens[cur].kind === "question") {
          isOptionalElem = true;
          elemRaw = elemRaw + "?";
          cur = cur + 1;
        }
        if (isOptionalElem) {
          elemTy = wrapNullability(elemTy, false, true);
        }
        elems.push(elemTy);
        elemRaws.push(elemRaw);
        if (cur < tokens.length && tokens[cur].kind === "comma") {
          cur = cur + 1;
          if (cur < tokens.length && tokens[cur].kind === "rbracket") {
            break;
          }
          continue;
        }
        break;
      }
    }
    if (cur >= tokens.length || tokens[cur].kind !== "rbracket") {
      return { kind: "err", error: "Expected ']' in tuple type" };
    }
    const raw = "[" + joinWith(elemRaws, ", ") + "]";
    if (elems.length === 0) {
      return { kind: "ok", ty: { kind: "array", elem: { kind: "unknown" } }, raw, nextPos: cur + 1 };
    }
    let homogeneous = true;
    let i = 1;
    while (i < elems.length) {
      //@ invariant 1 <= i && i <= elems.length
      //@ decreases elems.length - i
      if (!specTyEqual(elems[i], elems[0])) {
        homogeneous = false;
      }
      i = i + 1;
    }
    if (homogeneous) {
      return { kind: "ok", ty: { kind: "array", elem: elems[0] }, raw, nextPos: cur + 1 };
    }
    return { kind: "ok", ty: { kind: "tuple", elems }, raw, nextPos: cur + 1 };
  }

  // String literal type: "foo" or 'foo'
  if (tok.kind === "str") {
    return { kind: "ok", ty: { kind: "user", name: tok.text }, raw: tok.text, nextPos: pos + 1 };
  }

  // Numeric literal type: 0, 42
  if (tok.kind === "number") {
    return { kind: "ok", ty: { kind: "int" }, raw: tok.text, nextPos: pos + 1 };
  }

  // Negative numeric literal type: -1
  if (tok.kind === "minus") {
    if (pos + 1 >= tokens.length || tokens[pos + 1].kind !== "number") {
      return { kind: "err", error: "Expected numeric literal after '-'" };
    }
    return { kind: "ok", ty: { kind: "int" }, raw: "-" + tokens[pos + 1].text, nextPos: pos + 2 };
  }

  // Named / keyword / generic type reference: ident (.ident)* (<T, ...>)?
  if (tok.kind === "ident") {
    let name = tok.text;
    let cur = pos + 1;
    let hasDot = false;
    while (cur + 1 < tokens.length && tokens[cur].kind === "dot" && tokens[cur + 1].kind === "ident") {
      //@ invariant pos < cur && cur <= tokens.length
      //@ decreases tokens.length - cur
      name = name + "." + tokens[cur + 1].text;
      hasDot = true;
      cur = cur + 2;
    }
    if (cur < tokens.length && tokens[cur].kind === "lt") {
      cur = cur + 1;
      const args: SpecTy[] = [];
      const argRaws: string[] = [];
      if (cur >= tokens.length || tokens[cur].kind === "gt") {
        return { kind: "err", error: "Empty type argument list in '" + name + "<>'" };
      }
      while (true) {
        //@ invariant pos < cur && cur <= tokens.length
        //@ decreases tokens.length - cur
        const argRes = parseType(tokens, cur);
        if (argRes.kind === "err") return argRes;
        args.push(argRes.ty);
        argRaws.push(argRes.raw);
        cur = argRes.nextPos;
        if (cur < tokens.length && tokens[cur].kind === "comma") {
          cur = cur + 1;
          if (cur >= tokens.length || tokens[cur].kind === "gt") {
            return { kind: "err", error: "Trailing comma in type argument list" };
          }
          continue;
        }
        break;
      }
      if (cur >= tokens.length || tokens[cur].kind !== "gt") {
        return { kind: "err", error: "Expected '>' to close type arguments for '" + name + "'" };
      }
      cur = cur + 1;
      const fullRaw = name + "<" + joinWith(argRaws, ", ") + ">";
      if (!hasDot) {
        if (name === "Array" || name === "ReadonlyArray") {
          if (args.length !== 1) return { kind: "err", error: name + " expects exactly 1 type argument" };
          return { kind: "ok", ty: { kind: "array", elem: args[0] }, raw: fullRaw, nextPos: cur };
        }
        if (name === "Set" || name === "ReadonlySet") {
          if (args.length !== 1) return { kind: "err", error: name + " expects exactly 1 type argument" };
          return { kind: "ok", ty: { kind: "set", elem: args[0] }, raw: fullRaw, nextPos: cur };
        }
        if (name === "Map" || name === "ReadonlyMap" || name === "Record") {
          if (args.length !== 2) return { kind: "err", error: name + " expects exactly 2 type arguments" };
          return { kind: "ok", ty: { kind: "map", key: args[0], value: args[1] }, raw: fullRaw, nextPos: cur };
        }
        if (name === "Readonly") {
          if (args.length !== 1) return { kind: "err", error: name + " expects exactly 1 type argument" };
          return { kind: "ok", ty: args[0], raw: fullRaw, nextPos: cur };
        }
      }
      return { kind: "ok", ty: { kind: "user", name: fullRaw }, raw: fullRaw, nextPos: cur };
    }
    if (!hasDot) {
      if (name === "number" || name === "int") return { kind: "ok", ty: { kind: "int" }, raw: name, nextPos: cur };
      if (name === "bigint") return { kind: "ok", ty: { kind: "bigint" }, raw: name, nextPos: cur };
      if (name === "nat") return { kind: "ok", ty: { kind: "nat" }, raw: name, nextPos: cur };
      if (name === "real") return { kind: "ok", ty: { kind: "real" }, raw: name, nextPos: cur };
      if (name === "boolean" || name === "true" || name === "false") {
        return { kind: "ok", ty: { kind: "bool" }, raw: name, nextPos: cur };
      }
      if (name === "string") return { kind: "ok", ty: { kind: "string" }, raw: name, nextPos: cur };
      if (name === "null") return { kind: "ok", ty: { kind: "null" }, raw: name, nextPos: cur };
      if (name === "void" || name === "undefined") return { kind: "ok", ty: { kind: "void" }, raw: name, nextPos: cur };
      if (name === "unknown" || name === "any") return { kind: "ok", ty: { kind: "unknown" }, raw: name, nextPos: cur };
    }
    return { kind: "ok", ty: { kind: "user", name }, raw: name, nextPos: cur };
  }

  return { kind: "err", error: "Unexpected token '" + tok.text + "' in type annotation" };
}

// ── Entry points ─────────────────────────────────────────────

export function parseSpecTypeTokens(tokens: SpecTypeToken[]): SpecParseResult {
  //@ ensures tokens.length === 0 ==> \result.kind === "err"
  //@ ensures \result.kind === "ok" ==> \result.nextPos === tokens.length
  if (tokens.length === 0) {
    return { kind: "err", error: "Empty type annotation" };
  }
  const res = parseType(tokens, 0);
  if (res.kind === "err") return res;
  if (res.nextPos !== tokens.length) {
    return { kind: "err", error: "Unexpected trailing token '" + tokens[res.nextPos].text + "' in type annotation" };
  }
  return res;
}

export function parseSpecTypeKernel(input: string): SpecParseResult {
  const tokRes = tokenizeSpecType(input);
  if (tokRes.kind === "err") {
    return { kind: "err", error: tokRes.error };
  }
  return parseSpecTypeTokens(tokRes.tokens);
}
