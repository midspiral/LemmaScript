/**
 * leftPad — faithful translation of the original npm left-pad source.
 *
 * Original (Azer Koculu, 2014):
 *   function leftpad(str, len, ch) {
 *     str = String(str);
 *     var i = -1;
 *     if (!ch && ch !== 0) ch = ' ';
 *     len = len - str.length;
 *     while (++i < len) { str = ch + str; }
 *     return str;
 *   }
 *
 * Adaptations for LemmaScript:
 * - String(str) coercion dropped (input is already string)
 * - ch default dropped, replaced with requires ch.length === 1
 * - ++i from -1 → i from 0 (same iteration count)
 */
function leftPad(str: string, len: number, ch: string): string {
  //@ type len nat
  //@ type i nat
  //@ requires ch.length === 1
  //@ ensures str.length >= len ==> \result === str
  //@ ensures str.length < len ==> \result.length === len
  let result = str;
  len = len - str.length;
  let i = 0;
  while (i < len) {
    //@ invariant result.length === str.length + i
    //@ invariant i >= 0
    //@ invariant len > 0 ==> i <= len
    //@ invariant len <= 0 ==> result === str
    //@ decreases len - i
    result = ch + result;
    i = i + 1;
  }
  return result;
}
