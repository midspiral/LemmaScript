function containsDuplicate(nums: number[]): boolean {
    //@ ensures \result === true ==> exists(i: nat, exists(j: nat, i < j && i < nums.length && j < nums.length && nums[i] == nums[j]))
    //@ ensures \result === false ==> forall(i: nat, forall(j: nat, i < j && i < nums.length && j < nums.length ==> nums[i] != nums[j]))
    let numSet: Set<number> = new Set();
    for (let elem of nums) {
        //@ invariant forall(k: nat, k < _elem_idx && k < nums.length ==> numSet.has(nums[k]))
        //@ invariant forall(n: int, numSet.has(n) ==> exists(j: nat, j < _elem_idx && j < nums.length && nums[j] == n))
        //@ invariant forall(k1: nat, forall(k2: nat, k1 < k2 && k2 < _elem_idx && k1 < nums.length && k2 < nums.length ==> nums[k1] != nums[k2]))
        if (numSet.has(elem)) {
            return true;
        }
        numSet.add(elem);
    }
    return false;
}
