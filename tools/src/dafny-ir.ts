/**
 * Dafny IR — the intermediate representation between transform and emit.
 *
 * The dafny-transform phase produces these types.
 * The dafny-emit phase pretty-prints them to Dafny syntax.
 */

// ── Expressions ──────────────────────────────────────────────

export type DafnyExpr =
  | { kind: "var"; name: string }
  | { kind: "num"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "str"; value: string }
  | { kind: "binop"; op: string; left: DafnyExpr; right: DafnyExpr }
  | { kind: "unop"; op: string; expr: DafnyExpr }
  | { kind: "app"; fn: string; args: DafnyExpr[] }
  | { kind: "field"; obj: DafnyExpr; field: string }
  | { kind: "index"; seq: DafnyExpr; idx: DafnyExpr }
  | { kind: "seqLength"; seq: DafnyExpr }                     // |s|
  | { kind: "seqLiteral"; elems: DafnyExpr[] }                // [a, b, c]
  | { kind: "seqSlice"; seq: DafnyExpr; from: DafnyExpr | null; to: DafnyExpr | null }  // s[lo..hi]
  | { kind: "seqUpdate"; seq: DafnyExpr; idx: DafnyExpr; val: DafnyExpr }  // s[i := v]
  | { kind: "record"; fields: { name: string; value: DafnyExpr }[] }
  | { kind: "constructor"; name: string; args: DafnyExpr[] }  // Ctor(a, b)
  | { kind: "if"; cond: DafnyExpr; then: DafnyExpr; else: DafnyExpr }
  | { kind: "match"; scrutinee: DafnyExpr; arms: DafnyMatchArm[] }
  | { kind: "let"; name: string; value: DafnyExpr; body: DafnyExpr }
  | { kind: "forall"; vars: { name: string; type: string }[]; body: DafnyExpr }
  | { kind: "exists"; vars: { name: string; type: string }[]; body: DafnyExpr }

export interface DafnyMatchArm {
  pattern: string;
  body: DafnyExpr;
}

// ── Statements (method bodies) ──────────────────────────────

export type DafnyStmt =
  | { kind: "var"; name: string; type: string; mutable: boolean; value: DafnyExpr }
  | { kind: "assign"; target: string; value: DafnyExpr }
  | { kind: "return"; value: DafnyExpr }
  | { kind: "break" }
  | { kind: "if"; cond: DafnyExpr; then: DafnyStmt[]; else: DafnyStmt[] }
  | { kind: "match"; scrutinee: DafnyExpr; arms: DafnyStmtMatchArm[] }
  | { kind: "while"; cond: DafnyExpr; invariants: DafnyExpr[];
      decreases: DafnyExpr | null; body: DafnyStmt[] }

export interface DafnyStmtMatchArm {
  pattern: string;
  body: DafnyStmt[];
}

// ── Top-level declarations ──────────────────────────────────

export interface DafnyFunction {
  kind: "function";
  name: string;
  params: { name: string; type: string }[];
  returnType: string;
  requires: DafnyExpr[];
  decreases: DafnyExpr | null;
  body: DafnyExpr;
}

export interface DafnyMethod {
  kind: "method";
  name: string;
  params: { name: string; type: string }[];
  returns: { name: string; type: string }[];
  requires: DafnyExpr[];
  ensures: DafnyExpr[];
  decreases: DafnyExpr | null;
  body: DafnyStmt[];
}

export interface DafnyDatatype {
  kind: "datatype";
  name: string;
  constructors: { name: string; fields: { name: string; type: string }[] }[];
}

export interface DafnyPredicate {
  kind: "predicate";
  name: string;
  params: { name: string; type: string }[];
  body: DafnyExpr;
}

export type DafnyDecl = DafnyFunction | DafnyMethod | DafnyDatatype | DafnyPredicate;

export interface DafnyFile {
  comment: string;
  decls: DafnyDecl[];
}
