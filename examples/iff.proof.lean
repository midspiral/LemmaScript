import «iff.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct isEven by
  loom_solve
  simp only [Pure.isEven, decide_eq_true_eq]

prove_correct sameParity by
  loom_solve
  simp only [Pure.sameParity, decide_eq_true_eq]
  rw [Int.tmod_eq_emod_of_nonneg require_2, Int.tmod_eq_emod_of_nonneg require_1]
  omega
