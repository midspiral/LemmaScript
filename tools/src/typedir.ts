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
  | { kind: "real" }
  | { kind: "string" }
  | { kind: "void" }
  | { kind: "array"; elem: Ty }
  | { kind: "map"; key: Ty; value: Ty }
  | { kind: "set"; elem: Ty }
  | { kind: "optional"; inner: Ty }
  | { kind: "user"; name: string }
  | { kind: "unknown" }

export type CallKind = "pure" | "method" | "spec-pure" | "unknown"

/** Typed counterpart of RawChainStep. Carries the result-type at this step. */
export type TChainStep =
  | { kind: "field"; name: string; ty: Ty }
  | { kind: "call"; args: TExpr[]; ty: Ty; callKind: CallKind }
  | { kind: "index"; idx: TExpr; ty: Ty };

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
  | { kind: "record"; spread: TExpr | null; fields: { name: string; value: TExpr }[]; ty: Ty }
  | { kind: "arrayLiteral"; elems: TExpr[]; ty: Ty }
  | { kind: "lambda"; params: { name: string; ty: Ty }[]; body: TStmt[]; ty: Ty }
  | { kind: "conditional"; cond: TExpr; then: TExpr; else: TExpr; ty: Ty }
  | { kind: "optChain"; obj: TExpr; chain: TChainStep[]; ty: Ty }
  | { kind: "nullish"; left: TExpr; right: TExpr; ty: Ty }
  | { kind: "someMatch"; scrutinee: TExpr; binder: string; binderTy: Ty;
      someBody: TExpr; noneBody: TExpr; ty: Ty }
  // Spec-only (from //@ annotations):
  | { kind: "result"; ty: Ty }
  | { kind: "forall"; var: string; varTy: Ty; body: TExpr; ty: Ty }
  | { kind: "exists"; var: string; varTy: Ty; body: TExpr; ty: Ty }
  // Havoc — nondeterministic value:
  | { kind: "havoc"; ty: Ty }

// ── Statements ───────────────────────────────────────────────

export type TStmt =
  | { kind: "let"; name: string; ty: Ty; mutable: boolean; init: TExpr }
  | { kind: "assign"; target: string; value: TExpr }
  | { kind: "return"; value: TExpr }
  | { kind: "break" }
  | { kind: "continue" }
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
  | { kind: "forof"; names: string[]; nameTypes: Ty[]; iterable: TExpr;
      invariants: TExpr[]; doneWith: TExpr | null; body: TStmt[] }
  | { kind: "throw" }
  | { kind: "ghostLet"; name: string; ty: Ty; init: TExpr }
  | { kind: "ghostAssign"; target: string; value: TExpr }
  | { kind: "assert"; expr: TExpr }
  | { kind: "someMatch"; scrutinee: TExpr; binder: string; binderTy: Ty;
      someBody: TStmt[]; noneBody: TStmt[] }

// ── Top-level ────────────────────────────────────────────────

export interface TParam {
  name: string;
  ty: Ty;
}

export interface TFunction {
  name: string;
  typeParams: string[];
  params: TParam[];
  returnTy: Ty;
  requires: TExpr[];
  ensures: TExpr[];
  decreases: TExpr | null;
  isPure: boolean;          // no while, no mutable let
  forcePure: boolean;       // //@ pure — emit function by method if body can't be pure
  body: TStmt[];
}

export interface TClass {
  name: string;
  fields: { name: string; ty: Ty }[];
  methods: TFunction[];
}

export interface TConst {
  name: string;
  ty: Ty;
  value: TExpr;
}

export interface TModule {
  file: string;
  typeDecls: import("./types.js").TypeDeclInfo[];
  constants: TConst[];
  functions: TFunction[];
  classes: TClass[];
}
