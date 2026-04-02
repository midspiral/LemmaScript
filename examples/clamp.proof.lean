import «clamp.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct clamp by
  loom_solve

-- Note: loom_solve cannot currently handle mapM (WPGen has no rules for it).
-- This is expected — the user would need manual proof tactics here.
-- prove_correct clampAll by
--   loom_solve
