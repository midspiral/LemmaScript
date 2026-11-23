import type { RawStmt } from "./rawir.js";
import { targetPath, type AccessPath } from "./access-path.js";

type Exit = "normal" | "return" | "throw" | "break" | "continue";
type Effects = Map<Exit, AccessPath[]>;

function merge(into: Effects, from: Effects, prefix: AccessPath[] = []): void {
  for (const [exit, paths] of from) into.set(exit, [...(into.get(exit) ?? []), ...prefix, ...paths]);
}

/** Writes are attached to control-flow exits: a returning branch cannot
 * invalidate the continuation, but its writes still matter inside a loop. */
function block(stmts: readonly RawStmt[]): Effects {
  const result: Effects = new Map([["normal", []]]);
  for (const stmt of stmts) {
    const before = result.get("normal");
    if (!before) break;
    result.delete("normal");
    merge(result, statement(stmt), before);
  }
  return result;
}

function statement(s: RawStmt): Effects {
  switch (s.kind) {
    case "assign": case "ghostAssign": return new Map([["normal", [targetPath(s.target)]]]);
    case "return": case "throw": case "break": case "continue": return new Map([[s.kind, []]]);
    case "if": {
      const effects = block(s.then);
      merge(effects, block(s.else));
      return effects;
    }
    case "switch": {
      const effects = block(s.defaultBody);
      for (const c of s.cases) merge(effects, block(c.body));
      if (effects.has("break")) {
        merge(effects, new Map([["normal", effects.get("break")!]]));
        effects.delete("break");
      }
      return effects;
    }
    case "while": case "forof": {
      const effects = block(s.body);
      // Zero iterations are possible. Any iteration can precede an exit.
      const writes = [...effects.values()].flat();
      return new Map([["normal", writes], ...[...effects].filter(([exit]) => exit === "return" || exit === "throw")]);
    }
    case "let": case "ghostLet": case "expr": case "assert": return new Map([["normal", []]]);
  }
}

export function continuationWrites(stmt: RawStmt): AccessPath[] {
  return statement(stmt).get("normal") ?? [];
}

export function loopWrites(stmts: readonly RawStmt[]): AccessPath[] {
  return [...block(stmts).values()].flat();
}
