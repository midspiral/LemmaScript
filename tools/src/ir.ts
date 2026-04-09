/**
 * IR — the intermediate representation between transform and emit.
 *
 * The transform phase produces these types.
 * The emit phase pretty-prints them to backend syntax (Lean or Dafny).
 */

import type { Ty } from "./typedir.js";

// ── Expressions ──────────────────────────────────────────────

export type Expr =
  | { kind: "var"; name: string }
  | { kind: "num"; value: number }
  | { kind: "bool"; value: boolean }
  | { kind: "str"; value: string }
  | { kind: "constructor"; name: string; type?: string }       // .idle, .allow (type = parent datatype name)
  | { kind: "binop"; op: string; left: Expr; right: Expr }
  | { kind: "unop"; op: string; expr: Expr }
  | { kind: "app"; fn: string; args: Expr[] }            // f a b
  | { kind: "field"; obj: Expr; field: string }           // x.res, arr.size
  | { kind: "toNat"; expr: Expr }                               // expr.toNat
  | { kind: "index"; arr: Expr; idx: Expr }                // arr[idx]!
  | { kind: "record"; spread: Expr | null; fields: { name: string; value: Expr }[] }
  | { kind: "arrayLiteral"; elems: Expr[] }
  | { kind: "emptyMap" }
  | { kind: "emptySet" }
  | { kind: "methodCall"; obj: Expr; objTy: Ty; method: string; args: Expr[]; monadic: boolean }
  | { kind: "lambda"; params: { name: string; type: Ty }[]; body: Stmt[] }
  | { kind: "if"; cond: Expr; then: Expr; else: Expr }
  | { kind: "match"; scrutinee: string | Expr; arms: MatchArm[] }
  | { kind: "forall"; var: string; type: Ty; body: Expr }
  | { kind: "exists"; var: string; type: Ty; body: Expr }
  | { kind: "implies"; premises: Expr[]; conclusion: Expr }
  | { kind: "let"; name: string; value: Expr; body: Expr }

export interface MatchArm {
  pattern: string;    // ".syn seq", ".idle", "_"
  body: Expr;
}

// ── Statements ──────────────────────────────────────────────

export type Stmt =
  | { kind: "let"; name: string; type: Ty; mutable: boolean; value: Expr }
  | { kind: "assign"; target: string; value: Expr }
  | { kind: "bind"; target: string; value: Expr }         // x ← f a b (mutation)
  | { kind: "let-bind"; name: string; value: Expr }       // let x ← f a b (new binding)
  | { kind: "return"; value: Expr }
  | { kind: "break" }
  | { kind: "continue" }
  | { kind: "if"; cond: Expr; then: Stmt[]; else: Stmt[] }
  | { kind: "match"; scrutinee: string; arms: StmtMatchArm[] }
  | { kind: "while"; cond: Expr; invariants: Expr[]; decreasing: Expr | null;
      doneWith: Expr | null; body: Stmt[] }
  | { kind: "forin"; idx: string; bound: Expr; invariants: Expr[]; body: Stmt[] }
  | { kind: "ghostLet"; name: string; type: Ty; value: Expr }
  | { kind: "ghostAssign"; target: string; value: Expr }
  | { kind: "assert"; expr: Expr }

export interface StmtMatchArm {
  pattern: string;
  body: Stmt[];
}

// ── Top-level declarations ───────────────────────────────────

export interface Inductive {
  kind: "inductive";
  name: string;
  constructors: { name: string; fields: { name: string; type: Ty }[] }[];
  deriving: string[];
}

export interface Structure {
  kind: "structure";
  name: string;
  fields: { name: string; type: Ty }[];
  deriving: string[];
}

export interface FnDef {
  kind: "def";
  name: string;
  params: { name: string; type: Ty }[];
  returnType: Ty;
  requires: Expr[];  // used by Dafny backend; Lean backend ignores
  ensures: Expr[];   // used by Dafny backend for companion lemma
  body?: Expr;       // absent for abstract functions
}

export interface FnMethod {
  kind: "method";
  name: string;
  params: { name: string; type: Ty }[];
  returnType: Ty;
  requires: Expr[];
  ensures: Expr[];
  body: Stmt[];
}

export interface Namespace {
  kind: "namespace";
  name: string;
  decls: Decl[];
}

export interface ClassDecl {
  kind: "class";
  name: string;
  fields: { name: string; type: Ty }[];
  methods: FnMethod[];
}

export type Decl = Inductive | Structure | FnDef | FnMethod | Namespace | ClassDecl;

export interface Module {
  comment: string;
  imports: string[];
  options: { key: string; value: string }[];
  decls: Decl[];
}
