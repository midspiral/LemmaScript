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

// Freshness holds in the raw namespace but Dafny escaping runs *after*: the
// user param `_t0` escapes to `i_t0'` (dodging the user `i_t0`), so a generated
// ANF temp for `callee(_t0)` — raw-freshened to `_t0'` — must escape to `i_t0''`.
// Escaped in the raw namespace alone, temp and param both collapse to `i_t0'`.
export function callee(x: number): number {
  //@ verify
  //@ ensures \result === x + 1
  return x + 1;
}

export function tempClash(_t0: number, i_t0: number): number {
  //@ verify
  //@ ensures \result === (_t0 + 1) + (i_t0 + 1)
  let z = 0;
  z = callee(_t0) + callee(i_t0);
  return z;
}

// `.some` binder capture surviving Dafny escaping: the receiver `single(_x)`
// and the lambda binder `_x` both head for `i_x'`, so the binder must land on
// `i_x''` — else the receiver reads the bound var and the body is constant-true.
export function someEscCollision(_x: number, i_x: number): boolean {
  //@ verify
  //@ ensures \result ==> _x > 0
  return single(_x).some(_x => _x > 0);
}

// The out-parameter must dodge a body local even when it is only assigned or
// never read: a bare `let res` still declares `res`, so the emitter's method-body
// scan has to count bindings and assignment targets, not just references.
export function resAssignOnly(x: number): number {
  //@ verify
  //@ ensures \result === x
  let res = 0;
  res = 1;
  return x;
}
