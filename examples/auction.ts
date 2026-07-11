/**
 * Sealed-bid auction over a sparse bid book: `bids[i]` may be empty (`undefined`)
 * where a slot was withdrawn. `highestBid` returns the winning amount for an item,
 * never below its reserve; `firstFunded` finds the earliest usable bid.
 */

//@ backend dafny

type Bid = { key: string; amount: number };

// Winning bid amount for `key` — the max over matching bids, floored at the reserve.
function highestBid(bids: (Bid | undefined)[], key: string, reserve: number): number {
  //@ verify
  //@ ensures \result >= reserve
  let best = reserve;
  for (let i = 0; i < bids.length; i++) {
    //@ invariant best >= reserve
    const bid = bids[i];
    if (!bid || bid.key !== key) continue;
    if (bid.amount > best) best = bid.amount;
  }
  return best;
}

// Index of the first funded bid for `key` (present, positive amount), else -1.
function firstFunded(bids: (Bid | undefined)[], key: string): number {
  //@ verify
  //@ ensures \result === -1 || (0 <= \result && \result < bids.length)
  for (let i = 0; i < bids.length; i++) {
    //@ invariant 0 <= i && i <= bids.length
    const bid = bids[i];
    if (bid?.key !== key || bid.amount <= 0) continue;
    return i;
  }
  return -1;
}
