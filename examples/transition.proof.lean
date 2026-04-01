import «transition.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct transition by
  unfold Pure.transition; loom_solve

prove_correct runSession by
  loom_solve

-- Standalone property: if the last event is timeout, runSession returns idle.
open TotalCorrectness DemonicChoice in
theorem runSession_timeout_resets (events : Array Event)
    (h1 : events.size > 0) (h2 : lastEvent events = .timeout) :
    triple (events.size > 0 ∧ lastEvent events = .timeout)
           (runSession events)
           (fun res => res = State.idle) := by
  unfold runSession
  loom_solve
