/**
 * Typed IR — Raw IR annotated with resolved types and classifications.
 *
 * Produced by the resolve pass. Consumed by the transform.
 * Still TS-shaped (not Lean-shaped).
 */

// ── Types ────────────────────────────────────────────────────

export type Ty =
  | { kind: "bool" }
  | { kind: "nat" }
  | { kind: "int" }
  | { kind: "string" }
  | { kind: "void" }
  | { kind: "array"; elem: Ty }
  | { kind: "user"; name: string }
  | { kind: "unknown" }

export type CallKind = "pure" | "method" | "unknown"

// ── Expressions ──────────────────────────────────────────────

export type TExpr =
  | { kind: "var"; name: string; ty: Ty }
  | { kind: "num"; value: number; ty: Ty }
  | { kind: "str"; value: string; ty: Ty }
  | { kind: "bool"; value: boolean; ty: Ty }
  | { kind: "binop"; op: string; left: TExpr; right: TExpr; ty: Ty }
  | { kind: "unop"; op: string; expr: TExpr; ty: Ty }
  | { kind: "call"; fn: TExpr; args: TExpr[]; ty: Ty; callKind: CallKind }
  | { kind: "index"; obj: TExpr; idx: TExpr; ty: Ty }
  | { kind: "field"; obj: TExpr; field: string; ty: Ty;
      isDiscriminant?: boolean }            // true if this is a discriminant field access
  | { kind: "record"; fields: { name: string; value: TExpr }[]; ty: Ty }
  // Spec-only (from //@ annotations):
  | { kind: "result"; ty: Ty }
  | { kind: "forall"; var: string; varTy: Ty; body: TExpr; ty: Ty }
  | { kind: "exists"; var: string; varTy: Ty; body: TExpr; ty: Ty }

// ── Statements ───────────────────────────────────────────────

export type TStmt =
  | { kind: "let"; name: string; ty: Ty; mutable: boolean; init: TExpr }
  | { kind: "assign"; target: string; value: TExpr }
  | { kind: "return"; value: TExpr }
  | { kind: "break" }
  | { kind: "expr"; expr: TExpr }
  | { kind: "if"; cond: TExpr; then: TStmt[]; else: TStmt[] }
  | { kind: "while"; cond: TExpr;
      invariants: TExpr[];       // resolved from //@ annotation strings
      decreases: TExpr | null;
      doneWith: TExpr | null;
      body: TStmt[] }
  | { kind: "switch"; expr: TExpr; discriminant: string;
      cases: { label: string; body: TStmt[] }[];
      defaultBody: TStmt[] }

// ── Top-level ────────────────────────────────────────────────

export interface TParam {
  name: string;
  ty: Ty;
}

export interface TFunction {
  name: string;
  params: TParam[];
  returnTy: Ty;
  requires: TExpr[];
  ensures: TExpr[];
  isPure: boolean;          // no while, no mutable let
  body: TStmt[];
}

export interface TModule {
  file: string;
  typeDecls: import("./types.js").TypeDeclInfo[];
  functions: TFunction[];
}
