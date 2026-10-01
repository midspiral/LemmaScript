import assert from "node:assert/strict";
import { test } from "node:test";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import type { Ty } from "../src/typedir.ts";

function extract(source: string) {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: { strict: true, target: ScriptTarget.ESNext } });
  return extractModule(project.createSourceFile("input.ts", source));
}

test("callable interfaces use instantiated signatures, including imports and inheritance", () => {
  const project = new Project({ useInMemoryFileSystem: true, compilerOptions: { strict: true } });
  project.createSourceFile("predicate.ts", `export interface Predicate<in T> { (x:T):boolean }`);
  const file = project.createSourceFile("input.ts", `
    import type { Predicate } from "./predicate";
    interface Strings extends Predicate<string> {}
    export function invert(self:Strings):Predicate<string> { return x => !self(x); }
  `);
  const fn = resolveModule(extractModule(file)).functions[0];
  const predicate = { kind: "fn", params: [{ kind: "string" }], result: { kind: "bool" } };
  assert.deepEqual(fn.params[0].ty, predicate);
  assert.deepEqual(fn.returnTy, predicate);
});

for (const [label, shape] of [
  ["overloads", "(x:number):boolean; (x:string):boolean"],
  ["generic calls", "<T>(x:T):boolean"],
  ["properties", "(x:number):boolean; readonly label:string"],
  ["optional arguments", "(x?:number):boolean"],
  ["rest arguments", "(...xs:number[]):boolean"],
  ["this arguments", "(this:{value:number}, x:number):boolean"],
  ["constructors", "(x:number):boolean; new():object"],
  ["index signatures", "(x:number):boolean; [key:string]:unknown"],
] as const) {
  test(`callable interface extraction does not erase ${label}`, () => {
    const raw = extract(`interface Callable { ${shape} } export function keep(f:Callable):Callable { return f; }`);
    assert.equal(raw.functions[0].params[0].tsType, "Callable");
    assert.equal(raw.functions[0].returnType, "Callable");
  });
}

test("recursive callable interfaces fail explicitly, including through arrays", () => {
  for (const result of ["Recursive", "Recursive[]"]) {
    assert.throws(() => extract(`interface Recursive { (): ${result} } export function keep(f:Recursive):Recursive { return f; }`), /Recursive callable interfaces/);
  }
});

test("returned lambdas receive generic parameter types from their declared signature", () => {
  const raw = extract(`
    interface Predicate<A> { (value:A):boolean }
    export function negate<A>(self:Predicate<A>):Predicate<A> { return value => !self(value); }
    type Item = { enabled:boolean };
    export function bounded<A extends Item>():Predicate<A> { return value => value.enabled; }
  `);
  const returned = raw.functions[0].body[0];
  assert.equal(returned.kind, "return");
  if (returned.kind !== "return" || returned.value.kind !== "lambda") assert.fail("expected a returned lambda");
  assert.equal(returned.value.params[0].tsType, undefined, "extraction must leave the parameter contextual");
  const resolved = resolveModule(raw).functions[0].body[0];
  if (resolved.kind !== "return" || resolved.value.kind !== "lambda") assert.fail("expected a resolved lambda");
  assert.deepEqual(resolved.value.params[0].ty, { kind: "user", name: "A" });
  const bounded = resolveModule(raw).functions.find(fn => fn.name === "bounded")!.body[0];
  if (bounded.kind !== "return" || bounded.value.kind !== "lambda") assert.fail("expected a bounded lambda");
  assert.deepEqual(bounded.value.params[0].ty, { kind: "user", name: "Item" });
});

test("return context reaches nested and conditional closures without leaking into other callbacks", () => {
  const raw = extract(`
    type TaskId = number;
    export function choose(ids:TaskId[], yes:boolean):(prefix:string)=>(id:TaskId)=>boolean {
      const retained = ids.filter(id => id >= 0);
      return prefix => yes ? id => prefix.length > id : id => prefix.length < id;
    }
    export function explicit():(id:TaskId)=>boolean { return (id:number) => id > 0; }
  `);
  const typed = resolveModule(raw);
  const paramTypes: Ty[] = [];
  JSON.stringify(typed.functions.find(fn => fn.name === "choose")!.body, (_key, value) => {
    if (value?.kind === "lambda") paramTypes.push(...value.params.map((param: { ty: Ty }) => param.ty));
    return value;
  });
  const taskId: Ty = { kind: "user", name: "TaskId" };
  assert.deepEqual(paramTypes, [taskId, { kind: "string" }, taskId, taskId]);
  const explicit = typed.functions.find(fn => fn.name === "explicit")!.body[0];
  if (explicit.kind !== "return" || explicit.value.kind !== "lambda") assert.fail("expected an explicit lambda");
  assert.deepEqual(explicit.value.params[0].ty, { kind: "int" });
});
