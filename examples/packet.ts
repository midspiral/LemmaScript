/**
 * Packet processing — discriminated union with data fields.
 */

type Packet =
  | { tag: "syn"; seq: number }
  | { tag: "ack"; seq: number }
  | { tag: "data"; seq: number; len: number }
  | { tag: "fin" }

function nextSeq(state: number, pkt: Packet): number {
  //@ ensures pkt.tag === "syn" ==> \result === pkt.seq
  //@ ensures pkt.tag === "data" ==> \result === state + pkt.len
  //@ ensures pkt.tag === "fin" ==> \result === state

  if (pkt.tag === "syn") return pkt.seq;
  if (pkt.tag === "ack") return state;
  if (pkt.tag === "data") return state + pkt.len;
  return state;
}
