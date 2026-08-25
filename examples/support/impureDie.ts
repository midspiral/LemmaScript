/** Runtime implementation used by the cross-file impure-extern example. */

//@ impure
//@ ensures 1 <= \result && \result <= 6
export function rollDie(): number {
  return 1 + Math.floor(Math.random() * 6);
}
