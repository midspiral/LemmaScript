/**
 * Protocol state machine — verifying safety properties of event sequences.
 */

type State = "idle" | "connecting" | "connected" | "closing"
type Event = "connect" | "ack" | "close" | "timeout"

function transition(state: State, event: Event): State {
  //@ ensures event === "timeout" ==> \result === "idle"

  if (state === "idle" && event === "connect") return "connecting";
  if (state === "connecting" && event === "ack") return "connected";
  if (state === "connected" && event === "close") return "closing";
  if (state === "closing" && event === "ack") return "idle";
  if (event === "timeout") return "idle";
  return state;
}

function runSession(events: Event[]): State {
  //@ type i nat
  //@ requires events.length > 0
  //@ requires lastEvent(events) === "timeout"
  //@ ensures \result === "idle"

  let state: State = "idle";
  let i = 0;
  while (i < events.length) {
    //@ invariant i <= events.length
    //@ invariant i > 0 && events[i - 1] === "timeout" ==> state === "idle"
    //@ decreases events.length - i
    state = transition(state, events[i]);
    i = i + 1;
  }
  return state;
}
