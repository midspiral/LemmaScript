/**
 * Lean IR — the intermediate representation between transform and emit.
 *
 * The transform phase produces these types.
 * The emit phase pretty-prints them to Lean syntax.
 */

// ── Expressions ──────────────────────────────────────────────

export type LeanExpr =
  | { kind: "var"; name: string }
  | { kind: "num"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "str"; value: string }
  | { kind: "constructor"; name: string }                     // .idle, .allow
  | { kind: "binop"; op: string; left: LeanExpr; right: LeanExpr }
  | { kind: "unop"; op: string; expr: LeanExpr }
  | { kind: "app"; fn: string; args: LeanExpr[] }            // f a b
  | { kind: "field"; obj: LeanExpr; field: string }           // x.res, arr.size
  | { kind: "index"; arr: LeanExpr; idx: LeanExpr; toNat: boolean } // arr[i]! or arr[i.toNat]!
  | { kind: "record"; fields: { name: string; value: LeanExpr }[] }
  | { kind: "if"; cond: LeanExpr; then: LeanExpr; else: LeanExpr }
  | { kind: "match"; scrutinee: string; arms: LeanMatchArm[] }
  | { kind: "forall"; var: string; type: string; body: LeanExpr }
  | { kind: "exists"; var: string; type: string; body: LeanExpr }
  | { kind: "implies"; premises: LeanExpr[]; conclusion: LeanExpr }
  | { kind: "let"; name: string; value: LeanExpr; body: LeanExpr }

export interface LeanMatchArm {
  pattern: string;    // ".syn seq", ".idle", "_"
  body: LeanExpr;
}

// ── Statements (Velvet method bodies) ────────────────────────

export type LeanStmt =
  | { kind: "let"; name: string; type: string; mutable: boolean; value: LeanExpr }
  | { kind: "assign"; target: string; value: LeanExpr }
  | { kind: "bind"; target: string; value: LeanExpr }         // x ← f a b
  | { kind: "return"; value: LeanExpr }
  | { kind: "break" }
  | { kind: "if"; cond: LeanExpr; then: LeanStmt[]; else: LeanStmt[] }
  | { kind: "match"; scrutinee: string; arms: LeanStmtMatchArm[] }
  | { kind: "while"; cond: LeanExpr; invariants: LeanExpr[]; decreasing: LeanExpr | null;
      doneWith: LeanExpr | null; body: LeanStmt[] }

export interface LeanStmtMatchArm {
  pattern: string;
  body: LeanStmt[];
}

// ── Top-level declarations ───────────────────────────────────

export interface LeanInductive {
  kind: "inductive";
  name: string;
  constructors: { name: string; fields: { name: string; type: string }[] }[];
  deriving: string[];
}

export interface LeanStructure {
  kind: "structure";
  name: string;
  fields: { name: string; type: string }[];
  deriving: string[];
}

export interface LeanDef {
  kind: "def";
  name: string;
  params: { name: string; type: string }[];
  returnType: string;
  body: LeanExpr;
}

export interface LeanMethod {
  kind: "method";
  name: string;
  params: { name: string; type: string }[];
  returnType: string;
  requires: LeanExpr[];
  ensures: LeanExpr[];
  body: LeanStmt[];
}

export type LeanDecl = LeanInductive | LeanStructure | LeanDef | LeanMethod;

export interface LeanFile {
  comment: string;
  imports: string[];
  options: { key: string; value: string }[];
  decls: LeanDecl[];
}
