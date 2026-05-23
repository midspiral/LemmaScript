/**
 * A `//@ declare-type` shadows an alias whose real (TS) definition is a union
 * of object variants referencing types LemmaScript doesn't model (`MetaBlob`
 * here standing in for an SDK's `SharedV2ProviderOptions` etc.). Resolving the
 * parameter type must stop at the declare-type surface and NOT walk the union
 * into its variants — otherwise the generated Dafny carries datatypes for
 * `MetaBlob` and the synthetic variant records, none of which the verified
 * function uses, and which fail Dafny resolution.
 *
 * Mirrors the brownfield shape from mastra-ai/mastra where `ModelMessage` is
 * an imported union (`System|User|Assistant|Tool ModelMessage`) shadowed by a
 * `//@ declare-type ModelMessage { role, content }`.
 */

//@ backend dafny

// `when: Date` stands in for an SDK type LemmaScript doesn't model (like
// mastra's `SharedV2ProviderOptions`). If the union variants leak into the
// output, `Date` is referenced but never declared and Dafny resolution fails.
interface MetaBlob {
  a: number;
  when: Date;
}

interface TextMsg {
  kind: 'text';
  meta: MetaBlob;
}

interface DataMsg {
  kind: 'data';
  meta: MetaBlob;
}

type RawMsg = TextMsg | DataMsg;

//@ declare-type RawMsg { kind: string }

export function countMsgs(msgs: RawMsg[]): number {
  //@ verify
  //@ ensures \result >= 0
  return msgs.length;
}
