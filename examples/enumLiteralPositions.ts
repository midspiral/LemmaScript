/**
 * Contextual lowering of string-literal-union members.
 *
 * A bare `"ru"` becomes its datatype constructor (`Lang.ru`) when the position
 * it sits in has a known target type — that is what makes `x === "ru"` a
 * discriminant test rather than a string compare. Three shapes have to carry
 * that type further than the literal's immediate parent:
 *
 *   - A ternary's branches sit in the same target position as the ternary
 *     itself, so `return c ? "ru" : "en"` must lower like `return "ru"` /
 *     `return "en"` do. A `??` default is transparent the same way. Coercing
 *     the branches against *each other* only settles the mixed shape
 *     (`c ? lang : "en"`), where one side already carries the datatype.
 *   - An optional target (`Color | null`, `Color | undefined`) contributes the
 *     `Some(...)` wrap, so the literal has to be lowered against the payload
 *     type underneath the wrap rather than against the optional.
 *   - `const c = pick(n)` with no annotation: TS reports the widened
 *     `string | undefined`, and the string-union rescue has to see through the
 *     optional to recover `Color | undefined` — otherwise the narrowed payload
 *     is a bare string and `c === "red"` degrades to a string compare, taking
 *     the caller down with the callee.
 *
 * All three are value-side only: the `if`-statement spelling and the `ensures`
 * on the very same function already lowered correctly, so two spellings of one
 * function disagreed. See `coerceStr` (tools/src/resolve.ts).
 */

//@ backend dafny

type Lang = "en" | "ru";
type Color = "red" | "blue";
interface Doc { lang: Lang; n: number }

function idLang(l: Lang): Lang {
  //@ verify
  //@ ensures \result === l
  return l;
}

// ── Ternary branches ─────────────────────────────────────────

/** Ternary in return position. */
export function flipTernary(lang: Lang): Lang {
  //@ verify
  //@ ensures \result !== lang
  return lang === "en" ? "ru" : "en";
}

/** The same function as an `if` — the spelling that already lowered. */
export function flipIf(lang: Lang): Lang {
  //@ verify
  //@ ensures \result !== lang
  if (lang === "en") return "ru";
  return "en";
}

/** One branch already carries the datatype and hands it to the other. */
export function flipMixed(lang: Lang): Lang {
  //@ verify
  //@ ensures \result === lang || \result === "en"
  return lang === "ru" ? lang : "en";
}

/** Annotated `const` initializer. */
export function flipLet(lang: Lang): Lang {
  //@ verify
  //@ ensures \result !== lang
  const flipped: Lang = lang === "en" ? "ru" : "en";
  return flipped;
}

/** Call argument. */
export function flipArg(lang: Lang): Lang {
  //@ verify
  //@ ensures \result !== lang
  return idLang(lang === "en" ? "ru" : "en");
}

/** Record field. */
export function flipDoc(lang: Lang): Doc {
  //@ verify
  //@ ensures \result.lang !== lang
  return { lang: lang === "en" ? "ru" : "en", n: 0 };
}

/** `??` default — the nullish handler coerces a bare literal, and a ternary too. */
export function orDefault(lang: Lang | undefined, toRu: boolean): Lang {
  //@ verify
  //@ ensures lang !== undefined ==> \result === lang
  return lang ?? (toRu ? "ru" : "en");
}

// ── Under an optional wrap ───────────────────────────────────

/** `T | undefined` return: the literal lowers against the payload, then wraps. */
export function pick(n: number): Color | undefined {
  //@ verify
  //@ ensures n === 1 ==> \result === "red"
  //@ ensures n !== 1 && n !== 2 ==> \result === undefined
  if (n === 1) return "red";
  if (n === 2) return "blue";
  return undefined;
}

/** `T | null` behaves identically — both parse as `optional<T>`. */
export function pickNull(n: number): Color | null {
  //@ verify
  //@ ensures n === 1 ==> \result === "red"
  if (n === 1) return "red";
  return null;
}

/** Optional-typed `const`, initialized by a ternary — both gaps at once. */
export function pickLet(n: number): Color | undefined {
  //@ verify
  //@ ensures n === 1 ==> \result === "red"
  const c: Color | undefined = n === 1 ? "red" : undefined;
  return c;
}

/** A caller composing over the optional — the shape that blocks transitively. */
export function nameOf(n: number): string {
  //@ verify
  //@ ensures n === 1 ==> \result === "red"
  const c = pick(n);
  if (c === undefined) return "none";
  return c === "red" ? "red" : "blue";
}
