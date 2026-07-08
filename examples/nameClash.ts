// Name-clash gauntlet: user identifiers deliberately collide with names the
// toolchain synthesizes or mangles (see tools/src/names.ts). Each function
// pins its semantics with an ensures that fails — or makes the backend reject
// a duplicate variable — if binder/temp hygiene ever regresses. Shared by
// both backends; some collisions only bite in one (the object-rest binder is
// Dafny-only, `match` is a keyword only in Lean), the other keeps it honest.

// Object-rest binder capture (MID-350): Dafny's `.delete()` lowering wraps
// the receiver/key in a map comprehension whose binder collides with the
// parameter `k`. Unhygienic, the filter becomes `k != k` — the empty map —
// and the frame postcondition below is falsified.
export function delKey(d: Record<string, number>, k: string): Record<string, number> {
  //@ verify
  //@ ensures !\result.has(k)
  //@ ensures forall(j, j !== k && d.has(j) ==> \result.has(j) && \result.get(j) === d.get(j))
  const { [k]: _drop, ...rest } = d;
  return rest;
}

// `.some(n => …)` lowers to `exists n :: n in <receiver> && …` in Dafny with
// the receiver emitted inside the binder's scope; a receiver mentioning `n`
// must force the binder to `n'`, or the body is constant-true.
export function single(n: number): number[] {
  //@ verify
  //@ ensures \result.length === 1 && \result[0] === n
  return [n];
}

export function anyOdd(n: number): boolean {
  //@ verify
  //@ ensures \result ==> n % 2 === 1
  //@ ensures n % 2 === 1 ==> \result
  return single(n).some(n => n % 2 === 1);
}

// Dafny escapeName must stay injective per scope: the local `_x` mangles to
// `i_x`, which the parameter already owns — the local must prime, or both
// names merge and the function returns 1 for every input.
export function underscoreVsMangled(i_x: number): number {
  //@ verify
  //@ ensures \result === i_x
  const _x = 1;
  return i_x;
}

// Keyword mangling, same class: the parameter `match` mangles to `match_` in
// Dafny, which the local already owns (Lean guillemets it instead).
export function keywordVsMangled(match: number): number {
  //@ verify
  //@ ensures \result === match
  const match_ = 2;
  return match;
}

// The result binder must dodge a user `res`: as a Dafny method out-parameter
// (`res_`) and as Loom's return binder (`res'`) — unfreshened, the Lean
// ensures would read `res = res + 0`, self-referentially true.
export function passThrough(res: number): number {
  //@ verify
  //@ ensures \result === res + 0
  return res;
}

// The Dafny method out-parameter must also dodge a body local named `res`,
// or Dafny reports "Duplicate local-variable name".
export function sumTo(x: number): number {
  //@ verify
  //@ requires x >= 0
  //@ ensures \result >= 0
  let res = 0;
  let i = 0;
  while (i < x) {
    //@ invariant 0 <= i && i <= x
    //@ invariant res >= 0
    //@ decreases (x - i).toNat
    res = res + i;
    i = i + 1;
  }
  return res;
}
