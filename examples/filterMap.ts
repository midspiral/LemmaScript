/**
 * The `.map(x => … | undefined).filter(x => x !== undefined)` idiom (filterMap).
 *
 * The callback returns `Out | undefined`, so `.map` produces a `seq<Option<Out>>`;
 * the `.filter` with a defined-check (and an `o is Out` type guard) both drops the
 * Nones AND unwraps to `seq<Out>`. LemmaScript lowers the defined-filter to the
 * proven `SeqFilterSome` preamble — a plain `Map(.value, Filter(.Some?, …))` would
 * not verify, since `.value` is partial. Mirrors pi's `convertToLlm` tail.
 */

//@ backend dafny

interface In { keep: boolean; n: number }
interface Out { n: number }

export function pick(items: In[]): Out[] {
  //@ verify
  //@ ensures \result.length <= items.length
  return items
    .map((it): Out | undefined => {
      if (it.keep) return { n: it.n };
      return undefined;
    })
    .filter((o): o is Out => o !== undefined);
}
