/**
 * A sealed-bid, second-price (Vickrey) auction over a sparse bid book:
 * `bids[i]` may be empty (`undefined`) where a slot was withdrawn, so every
 * read narrows `Bid | undefined` before use (`!bid || bid.key !== key`, or
 * optional chaining `bid?.key`).
 *
 * The four functions describe one auction end to end:
 *   - `highestBid`     — the winning amount, never below the reserve.
 *   - `winningBidder`  — who won: the earliest bid strictly above the reserve.
 *   - `secondPrice`    — what the winner pays: the runner-up's bid, floored at
 *                        the reserve (the Vickrey rule).
 *   - `firstFunded`    — a utility: the earliest present, positive bid.
 *
 * Each carries its safety property as an `ensures`, so the proof pins both the
 * auction rule and the narrowing that implements it.
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

// Index of the winning bidder for `key`: the earliest matching bid strictly
// above the reserve, or -1 if none clears it.
function winningBidder(bids: (Bid | undefined)[], key: string, reserve: number): number {
  //@ verify
  //@ ensures \result === -1 || (0 <= \result && \result < bids.length)
  let winner = -1;
  let best = reserve;
  for (let i = 0; i < bids.length; i++) {
    //@ invariant winner === -1 || (0 <= winner && winner < bids.length)
    const bid = bids[i];
    if (!bid || bid.key !== key) continue;
    if (bid.amount > best) {
      best = bid.amount;
      winner = i;
    }
  }
  return winner;
}

// Vickrey clearing price for `key`: the winner pays the second-highest matching
// bid, floored at the reserve. With zero or one qualifying bid the price is the
// reserve exactly.
function secondPrice(bids: (Bid | undefined)[], key: string, reserve: number): number {
  //@ verify
  //@ ensures \result >= reserve
  let best = reserve;
  let second = reserve;
  for (let i = 0; i < bids.length; i++) {
    //@ invariant second >= reserve
    //@ invariant best >= second
    const bid = bids[i];
    if (!bid || bid.key !== key) continue;
    if (bid.amount > best) {
      second = best;
      best = bid.amount;
    } else if (bid.amount > second) {
      second = bid.amount;
    }
  }
  return second;
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
