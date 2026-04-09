/**
 * Raw IR — structured AST for expressions and statements.
 *
 * Produced by the extract phase (ts-morph → RawExpr for body expressions)
 * and the specparser (annotation strings → RawExpr for spec expressions).
 *
 * Layer 1: structured (no strings for expressions)
 * Layer 2 (planned): add Ty to each node
 */

// ── Expressions ──────────────────────────────────────────────

export type RawExpr =
  | { kind: "var"; name: string }
  | { kind: "num"; value: number }
  | { kind: "str"; value: string }
  | { kind: "bool"; value: boolean }
  | { kind: "binop"; op: string; left: RawExpr; right: RawExpr }
  | { kind: "unop"; op: string; expr: RawExpr }
  | { kind: "call"; fn: RawExpr; args: RawExpr[] }
  | { kind: "index"; obj: RawExpr; idx: RawExpr }
  | { kind: "field"; obj: RawExpr; field: string }
  | { kind: "record"; spread: RawExpr | null; fields: { name: string; value: RawExpr }[] }
  | { kind: "arrayLiteral"; elems: RawExpr[] }
  | { kind: "lambda"; params: { name: string; tsType?: string }[]; body: RawExpr | RawStmt[] }
  | { kind: "conditional"; cond: RawExpr; then: RawExpr; else: RawExpr }  // ternary ? :
  | { kind: "emptyCollection"; collectionType: "Map" | "Set"; tsType: string }  // new Map<K,V>() / new Set<T>()
  | { kind: "nonNull"; expr: RawExpr }   // expr! (non-null assertion)
  // Spec-only (from //@ annotations, produced by specparser):
  | { kind: "result" }                                    // \result
  | { kind: "forall"; var: string; varType: "nat" | "int"; body: RawExpr }
  | { kind: "exists"; var: string; varType: "nat" | "int"; body: RawExpr }

// ── Statements ───────────────────────────────────────────────

export interface RawLet {
  kind: "let";
  name: string;
  mutable: boolean;
  tsType: string;      // raw TS type string, resolved later
  init: RawExpr;
  line: number;
}

export interface RawAssign {
  kind: "assign";
  target: string;
  value: RawExpr;
  line: number;
}

export interface RawReturn {
  kind: "return";
  value: RawExpr;
  line: number;
}

export interface RawBreak {
  kind: "break";
  line: number;
}

export interface RawContinue {
  kind: "continue";
  line: number;
}

export interface RawExprStmt {
  kind: "expr";
  expr: RawExpr;
  line: number;
}

export interface RawIf {
  kind: "if";
  cond: RawExpr;
  then: RawStmt[];
  else: RawStmt[];
  line: number;
}

export interface RawWhile {
  kind: "while";
  cond: RawExpr;
  invariants: string[];  decreases: string | null;
  doneWith: string | null;
  body: RawStmt[];
  line: number;
}

export interface RawSwitch {
  kind: "switch";
  expr: RawExpr;
  discriminant: string;     // field name if x.field, empty if just x
  cases: { label: string; body: RawStmt[] }[];
  defaultBody: RawStmt[];
  line: number;
}

export interface RawForOf {
  kind: "forof";
  names: string[];        // single name or destructured: [k, v, ...]
  iterable: RawExpr;
  invariants: string[];  doneWith: string | null;
  body: RawStmt[];
  line: number;
}

export interface RawThrow {
  kind: "throw";
  line: number;
}

export interface RawGhostLet {
  kind: "ghostLet";
  name: string;
  tsType: string | null;   // explicit type annotation, or null to infer
  init: string;            // spec expression string (parsed later)
  line: number;
}

export interface RawGhostAssign {
  kind: "ghostAssign";
  target: string;
  value: string;           // spec expression string (parsed later)
  line: number;
}

export interface RawAssert {
  kind: "assert";
  expr: string;              // spec expression string (parsed later)
  line: number;
}

export type RawStmt = RawLet | RawAssign | RawReturn | RawBreak | RawContinue | RawExprStmt | RawIf | RawWhile | RawSwitch | RawForOf | RawThrow | RawGhostLet | RawGhostAssign | RawAssert;

// ── Top-level ────────────────────────────────────────────────

export interface RawParam {
  name: string;
  tsType: string;
}

export interface RawFunction {
  name: string;
  params: RawParam[];
  returnType: string;
  requires: string[];     // //@ annotation strings
  ensures: string[];
  typeAnnotations: { name: string; type: string }[];
  body: RawStmt[];
  line: number;
}

export interface RawModule {
  file: string;
  typeDecls: import("./types.js").TypeDeclInfo[];
  functions: RawFunction[];
}
