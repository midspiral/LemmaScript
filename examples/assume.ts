/**
 * //@ assume — trusted assumption, the //@ assert-shaped sibling that
 * the verifier takes as given. Canonical use: constrain a //@ havoc'd
 * value inline in TS rather than post-hoc in the generated .dfy file.
 */
//@ backend dafny

export function shortenString(text: string): number {
  //@ verify
  //@ ensures \result >= 0 && \result <= text.length
  //@ havoc
  const cleaned = text.replace(/[^a-z]/g, '');
  //@ assume cleaned.length <= text.length
  return cleaned.length;
}
