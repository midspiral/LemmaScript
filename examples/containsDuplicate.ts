//@ backend dafny
// LeetCode 217 (Contains Duplicate I) and 219 (Contains Duplicate II).
//
// Adapted from
//   https://dev.to/hath995/contains-duplicate-i-38bo
//   https://dev.to/hath995/verify-contains-duplicate-ii-5b50

function containsDuplicate(nums: number[]): boolean {
    //@ ensures implies($result === true, exists((i: nat) => exists((j: nat) => i < j && i < nums.length && j < nums.length && nums[i] === nums[j])))
    //@ ensures implies($result === false, forall((i: nat) => forall((j: nat) => implies(i < j && i < nums.length && j < nums.length, nums[i] !== nums[j]))))
    let numSet: Set<number> = new Set();
    for (let elem of nums) {
        //@ invariant forall((k: nat) => implies(k < _elem_idx && k < nums.length, numSet.has(nums[k])))
        //@ invariant forall((n: int) => implies(numSet.has(n), exists((j: nat) => j < _elem_idx && j < nums.length && nums[j] === n)))
        //@ invariant forall((k1: nat) => forall((k2: nat) => implies(k1 < k2 && k2 < _elem_idx && k1 < nums.length && k2 < nums.length, nums[k1] !== nums[k2])))
        if (numSet.has(elem)) {
            return true;
        }
        numSet.add(elem);
    }
    return false;
}

function containsNearbyDuplicate(nums: number[], k: number): boolean {
    //@ type k nat
    //@ type i nat
    //@ requires k <= nums.length
    //@ ensures implies($result === true, exists((a: nat) => exists((b: nat) => a < b && b < nums.length && b - a <= k && nums[a] === nums[b])))
    //@ ensures implies($result === false, forall((a: nat) => forall((b: nat) => implies(a < b && b < nums.length && b - a <= k, nums[a] !== nums[b]))))
    let windowSet: Set<number> = new Set();
    const n = nums.length;
    if (k === 0) return false;
    let i = 0;
    while (i < n) {
        //@ invariant 0 <= i && i <= n
        //@ invariant implies(i < k, forall((x: int) => implies(x in windowSet, exists((j: nat) => j < i && nums[j] === x))))
        //@ invariant implies(i >= k, forall((x: int) => implies(x in windowSet, exists((j: nat) => i - k <= j && j < i && nums[j] === x))))
        //@ invariant implies(i < k, forall((j: nat) => implies(j < i, nums[j] in windowSet)))
        //@ invariant implies(i >= k, forall((j: nat) => implies(i - k <= j && j < i, nums[j] in windowSet)))
        //@ invariant forall((a: nat) => forall((b: nat) => implies(a < b && b < i && b - a <= k, nums[a] !== nums[b])))
        //@ decreases n - i
        if (windowSet.has(nums[i])) {
            return true;
        }
        if (i >= k) {
            windowSet.delete(nums[i - k]);
        }
        windowSet.add(nums[i]);
        i = i + 1;
    }
    return false;
}
