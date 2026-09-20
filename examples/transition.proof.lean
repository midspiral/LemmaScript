import «transition.def»

set_option velvet.semantics.termination "total"

prove_correct transition by
  velvet_vcgen [transition] with finish [Pure.transition]

prove_correct runSession by
  velvet_vcgen [runSession] with finish

-- Standalone property: if the last event is timeout, runSession returns idle.
open Std.Internal.Do in
theorem runSession_timeout_resets (events : Array Event)
    (h1 : events.size > 0) (h2 : lastEvent events = .timeout) :
    Triple (runSession events)
           (events.size > 0 ∧ lastEvent events = .timeout)
           (fun res => res = State.idle) False := by
  velvet_vcgen [runSession] with finish
