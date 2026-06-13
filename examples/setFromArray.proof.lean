import «setFromArray.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct member by
  loom_solve
  simp only [Pure.member]
  grind [List.contains_iff_mem, Array.mem_iff_getElem]
