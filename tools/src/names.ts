/**
 * Fresh-name authority for toolchain-minted identifiers.
 *
 * Several passes synthesize names — loop counters (`_x_idx`), lift temps
 * (`_t0`), someMatch binders (`_task_val`), comprehension binders, result
 * out-parameters. Any such name can collide with a user-written identifier
 * and either capture it (silently changing semantics — the `.delete()`
 * binder bug) or shadow it (a loud duplicate-variable error in the backend).
 *
 * The rule that kills both classes with zero churn to existing output:
 *
 *   a minted name is used verbatim UNLESS it collides with a user-written
 *   name in the scope it will live in, in which case a prime (`'`) is
 *   appended.
 *
 * TypeScript identifiers cannot contain a prime, while Dafny and Lean both
 * accept them, so a single prime always moves a name out of user space; and
 * priming preserves distinctness among minted names, so the existing
 * counter/suffix schemes keep working unchanged.
 *
 * Collisions are checked per function, not per module — an unrelated `k` in
 * some other function must not force a prime here. extract.ts seeds, per
 * function and for the module level (decl names, top-level consts):
 *   - source names: every Identifier token in that scope (a deliberate
 *     over-approximation: fields, callees, types all count)
 *   - spec names: identifier-shaped tokens inside `//@` comment text, which
 *     are not Identifier AST nodes and are otherwise invisible
 * Passes bracket their per-function work with enterFunction(name); minting
 * outside any function (or in a function extract didn't index) falls back to
 * the module-level names alone.
 */

interface NameSets { src: Set<string>; spec: Set<string> }

let _module: NameSets = { src: new Set(), spec: new Set() };
let _perFn = new Map<string, NameSets>();
let _cur: NameSets | null = null;

export function setUserNames(module_: NameSets, perFn: Map<string, NameSets>): void {
  _module = module_;
  _perFn = perFn;
  _cur = null;
}

export function enterFunction(name: string | null): void {
  _cur = name === null ? null : _perFn.get(name) ?? null;
}

/** Identifier-shaped tokens of a text fragment. Over-approximates (matches
 *  inside string literals too), which only ever costs an unnecessary prime. */
export function identTokens(text: string): Set<string> {
  return new Set(Array.from(text.matchAll(/[A-Za-z_][A-Za-z0-9_']*/g), m => m[0]));
}

function inSrc(name: string): boolean {
  return _module.src.has(name) || (_cur !== null && _cur.src.has(name));
}

function inSpec(name: string): boolean {
  return _module.spec.has(name) || (_cur !== null && _cur.spec.has(name));
}

/** Did the user write this name in the current scope — source or spec text? */
export function isUserName(name: string): boolean {
  return inSrc(name) || inSpec(name);
}

export function isSpecName(name: string): boolean {
  return inSpec(name);
}

/** Mint a toolchain-internal name: `base` verbatim, primed on collision with
 *  a user-written name in the current scope. `specVisible` marks names that
 *  are part of the readable generated surface (for-of index counters,
 *  someMatch binders) — user specs may legitimately reference those, so a
 *  spec mention is a reference, not a collision, and only TS-source names
 *  are avoided. */
export function mintName(base: string, opts?: { specVisible?: boolean }): string {
  if (inSrc(base) || (!opts?.specVisible && inSpec(base))) return base + "'";
  return base;
}
