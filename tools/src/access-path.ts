import type { RawExpr } from "./rawir.js";
import type { TExpr } from "./typedir.js";

/** A storage location that can be read without evaluating an index or call. */
export interface AccessPath { rootVar: string; fields: string[] }

export function accessPath(e: RawExpr | TExpr): AccessPath | null {
  if (e.kind === "var") return { rootVar: e.name, fields: [] };
  if (e.kind !== "field") return null;
  const parent = accessPath(e.obj);
  return parent && { rootVar: parent.rootVar, fields: [...parent.fields, e.field] };
}

export function targetPath(target: string): AccessPath {
  const [rootVar, ...fields] = target.split(".");
  return { rootVar, fields };
}

export function containsPath(parent: AccessPath, child: AccessPath): boolean {
  return parent.rootVar === child.rootVar && parent.fields.length <= child.fields.length &&
    parent.fields.every((field, i) => field === child.fields[i]);
}

export function samePath(a: AccessPath, b: AccessPath): boolean {
  return a.fields.length === b.fields.length && containsPath(a, b);
}
