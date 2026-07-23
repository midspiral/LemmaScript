import «binarySearch.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct sortedFrom by
  loom_solve

prove_correct sorted by
  loom_solve

-- The two interesting VCs are the halving steps: discarding a half is sound only
-- because sortedness is monotone (`sorted_mono` in the .spec file, proved from
-- the adjacent-pair definition compiled out of the TypeScript). The rest is
-- arithmetic. `require_1 : Pure.sorted arr = true` is cleared before `grind` on
-- those goals — left in place, `grind` diverges on the recursive definition.
prove_correct binarySearch by
  loom_goals_intro
  loom_unfold
  all_goals (try (clear require_1; grind))
  -- arr[mid] < target: nothing at or below mid can be target.
  · intro k hk0 hk
    have h := sorted_mono arr require_1 k.toNat ((lo + hi) / 2).toNat (by omega) (by omega)
    omega
  -- arr[mid] > target: nothing at or above mid can be target.
  · intro k hk hks
    have h := sorted_mono arr require_1 ((lo + hi) / 2).toNat k.toNat (by omega) (by omega)
    omega
