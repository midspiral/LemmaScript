/**
 * A `switch` inside a `.map` callback. Dafny and Lean model lambdas as single
 * expressions, so LemmaScript flattens the switch-with-returns body to a `match`
 * expression — the same switch→match lowering it does for function bodies, one
 * level wider (an arm that doesn't return falls through into the rest). Mirrors
 * pi's `convertToLlm`, whose `.map` callback switches on the message role.
 */

//@ backend dafny

interface UserMsg { role: "user"; text: string }
interface SysMsg { role: "system"; code: number }
type Msg = UserMsg | SysMsg;

/** Map each message to a numeric priority by role. */
export function priorities(msgs: Msg[]): number[] {
  //@ verify
  //@ ensures \result.length === msgs.length
  return msgs.map((m): number => {
    switch (m.role) {
      case "user":
        return 1;
      case "system":
        return 2;
    }
  });
}
