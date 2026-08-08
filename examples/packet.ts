/**
 * Packet processing — discriminated union with data fields.
 */

type Packet =
  | { tag: "syn"; seq: number }
  | { tag: "ack"; seq: number }
  | { tag: "data"; seq: number; len: number }
  | { tag: "fin" }

function nextSeq(state: number, pkt: Packet): number {
  //@ ensures implies(pkt.tag === "syn", $result === pkt.seq)
  //@ ensures implies(pkt.tag === "data", $result === state + pkt.len)
  //@ ensures implies(pkt.tag === "fin", $result === state)

  if (pkt.tag === "syn") return pkt.seq;
  if (pkt.tag === "ack") return state;
  if (pkt.tag === "data") return state + pkt.len;
  return state;
}
