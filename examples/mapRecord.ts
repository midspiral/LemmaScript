/**
 * Constructing a named record inside a `.map` callback. The callback's return
 * annotation (`(it): Out => …`) types the record literal to `Out`, so it lowers
 * to the `Out(...)` constructor (not an anonymous tuple) and the `Out` datatype
 * is emitted. Bread-and-butter for any DTO/union-transformer mapping.
 */

//@ backend dafny

interface In { tag: string; n: number }
interface Out { label: string; doubled: number }

export function relabel(items: In[]): Out[] {
  //@ verify
  //@ ensures \result.length === items.length
  return items.map((it): Out => ({ label: it.tag, doubled: it.n * 2 }));
}
