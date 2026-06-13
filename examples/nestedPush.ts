/**
 * Pushing to a nested array field mutates the record: `b.items.push(v)` must
 * lower to `b := b.(items := b.items + [v])`, not silently no-op.
 */

interface Bag { items: number[] }

export function pushItem(items: number[], v: number): number[] {
  //@ ensures \result.length === items.length + 1
  //@ ensures \result[items.length] === v
  const b: Bag = { items };
  b.items.push(v);
  return b.items;
}
