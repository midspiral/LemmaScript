/**
 * Multi-statement lambda body in a `.filter` callback. Dafny lambdas are
 * expression-only; the transform flattens the if/let/return-shaped body into a
 * single `return <expr>` (using the IR's `Expr.if` / `Expr.let` nodes), which
 * both backends' single-return-lambda fast path then emits.
 *
 *   { if (c) return v; const x = e; return r }
 *     →  return (if c then v else (let x = e in r))
 *
 * Mirrors mastra's `sanitizeOrphanedToolPairs` filter:
 *   p => { if (p.type !== 'tool-call') return true; const tc = p; return ... }
 */

//@ backend dafny

interface Part {
  type: string;
  providerExecuted?: boolean;
  toolCallId: string;
}

export function keepParts(parts: Part[], valid: Set<string>): Part[] {
  //@ verify
  //@ ensures \result.length <= parts.length
  return parts.filter(p => {
    if (p.type !== 'tool-call') return true;
    const tc = p;
    return tc.providerExecuted === true || valid.has(tc.toolCallId);
  });
}
