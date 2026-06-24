//@ backend dafny

/**
 * Count Bad Pairs (LeetCode 2364).
 *
 * A "good" pair (i, j) with i < j satisfies j - i == nums[j] - nums[i],
 * equivalently nums[j] - j == nums[i] - i. A bad pair is any other
 * ordered pair with i < j. There are n*(n-1)/2 ordered pairs total,
 * so badPairs = total - goodPairs.
 *
 * The file contains:
 *   1. Pair — record type for an (i, j) pair of nat indices.
 *   2. allPairsImpl / goodPairsImpl / badPairsImpl — iterative
 *      reference specifications that build the sets explicitly.
 *      Marked //@ pure so they can appear in `ensures` clauses;
 *      LemmaScript emits each as a Dafny `function by method`,
 *      with the spec body filled in (in countBadPairs.dfy) as the
 *      matching set comprehension. Dafny verifies the imperative
 *      body produces the comprehension.
 *   3. countBadPairsNaive (O(n^2)) and countBadPairs (O(n) via diffMap),
 *      both with `\result === badPairsImpl(nums).size` postcondition.
 *      The deep proof connecting the counter to |BadPairs(nums)|
 *      lives in countBadPairs.dfy.
 */

interface Pair {
  i: number //@ type nat
  j: number //@ type nat
}

//@ pure
export function allPairsImpl(nums: number[]): Set<Pair> {
  //@ type i nat
  //@ type j nat
  let result = new Set<Pair>();
  let i = 0;
  while (i < nums.length) {
    //@ invariant 0 <= i && i <= nums.length
    //@ invariant forall(p: Pair, p in result ==> p.i < i && p.j < nums.length && p.i < p.j)
    //@ invariant forall(x: nat, forall(y: nat, x < i && y < nums.length && x < y ==> {i: x, j: y} in result))
    //@ decreases nums.length - i
    let j = i + 1;
    while (j < nums.length) {
      //@ invariant i + 1 <= j && j <= nums.length
      //@ invariant forall(p: Pair, p in result ==> (p.i < i && p.j < nums.length && p.i < p.j) || (p.i === i && p.i < p.j && p.j < j))
      //@ invariant forall(x: nat, forall(y: nat, x < i && y < nums.length && x < y ==> {i: x, j: y} in result))
      //@ invariant forall(y: nat, i < y && y < j ==> {i: i, j: y} in result)
      //@ decreases nums.length - j
      result.add({ i: i, j: j });
      j = j + 1;
    }
    i = i + 1;
  }
  return result;
}

//@ pure
export function goodPairsImpl(nums: number[]): Set<Pair> {
  //@ type i nat
  //@ type j nat
  let result = new Set<Pair>();
  let i = 0;
  while (i < nums.length) {
    //@ invariant 0 <= i && i <= nums.length
    //@ invariant forall(p: Pair, p in result ==> p.i < i && p.j < nums.length && p.i < p.j && nums[p.j] - nums[p.i] === p.j - p.i)
    //@ invariant forall(x: nat, forall(y: nat, x < i && y < nums.length && x < y && nums[y] - nums[x] === y - x ==> {i: x, j: y} in result))
    //@ decreases nums.length - i
    let j = i + 1;
    while (j < nums.length) {
      //@ invariant i + 1 <= j && j <= nums.length
      //@ invariant forall(p: Pair, p in result ==> (p.i < i && p.j < nums.length && p.i < p.j && nums[p.j] - nums[p.i] === p.j - p.i) || (p.i === i && p.i < p.j && p.j < j && nums[p.j] - nums[p.i] === p.j - p.i))
      //@ invariant forall(x: nat, forall(y: nat, x < i && y < nums.length && x < y && nums[y] - nums[x] === y - x ==> {i: x, j: y} in result))
      //@ invariant forall(y: nat, i < y && y < j && nums[y] - nums[i] === y - i ==> {i: i, j: y} in result)
      //@ decreases nums.length - j
      if (nums[j] - nums[i] === j - i) {
        result.add({ i: i, j: j });
      }
      j = j + 1;
    }
    i = i + 1;
  }
  return result;
}

//@ pure
export function badPairsImpl(nums: number[]): Set<Pair> {
  //@ type i nat
  //@ type j nat
  let result = new Set<Pair>();
  let i = 0;
  while (i < nums.length) {
    //@ invariant 0 <= i && i <= nums.length
    //@ invariant forall(p: Pair, p in result ==> p.i < i && p.j < nums.length && p.i < p.j && nums[p.j] - nums[p.i] !== p.j - p.i)
    //@ invariant forall(x: nat, forall(y: nat, x < i && y < nums.length && x < y && nums[y] - nums[x] !== y - x ==> {i: x, j: y} in result))
    //@ decreases nums.length - i
    let j = i + 1;
    while (j < nums.length) {
      //@ invariant i + 1 <= j && j <= nums.length
      //@ invariant forall(p: Pair, p in result ==> (p.i < i && p.j < nums.length && p.i < p.j && nums[p.j] - nums[p.i] !== p.j - p.i) || (p.i === i && p.i < p.j && p.j < j && nums[p.j] - nums[p.i] !== p.j - p.i))
      //@ invariant forall(x: nat, forall(y: nat, x < i && y < nums.length && x < y && nums[y] - nums[x] !== y - x ==> {i: x, j: y} in result))
      //@ invariant forall(y: nat, i < y && y < j && nums[y] - nums[i] !== y - i ==> {i: i, j: y} in result)
      //@ decreases nums.length - j
      if (nums[j] - nums[i] !== j - i) {
        result.add({ i: i, j: j });
      }
      j = j + 1;
    }
    i = i + 1;
  }
  return result;
}

export function countBadPairsNaive(nums: number[]): number {
  //@ requires nums.length > 0
  //@ ensures \result >= 0
  //@ ensures \result === badPairsImpl(nums).size
  //@ type i nat
  //@ type k nat
  let count = 0;
  const n = nums.length;

  let i = 0;
  while (i < n - 1) {
    //@ invariant 0 <= i && i <= n - 1
    //@ invariant count >= 0
    //@ decreases (n - 1) - i
    const iprime = nums[i] - i;
    let k = i + 1;
    while (k < n) {
      //@ invariant i + 1 <= k && k <= n
      //@ invariant count >= 0
      //@ decreases n - k
      if (nums[k] - k === iprime) {
        count = count + 1;
      }
      k = k + 1;
    }
    i = i + 1;
  }

  const pairs = Math.floor((n - 1) * n / 2) - count;
  return pairs;
}

export function countBadPairs(nums: number[]): number {
  //@ requires nums.length > 0
  //@ ensures \result >= 0
  //@ ensures \result === badPairsImpl(nums).size
  //@ type i nat
  let goodCount = 0;
  const n = nums.length;
  const diffMap: Map<number, number> = new Map();
  let i = 0;
  while (i < n) {
    //@ invariant 0 <= i && i <= n
    //@ invariant goodCount >= 0
    //@ decreases n - i
    const diff = nums[i] - i;
    const count = diffMap.get(diff) ?? 0;
    goodCount = goodCount + count;
    diffMap.set(diff, count + 1);
    i = i + 1;
  }
  return Math.floor((n - 1) * n / 2) - goodCount;
}
