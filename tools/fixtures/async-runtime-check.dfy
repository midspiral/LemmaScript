// Executable checks of the generated state machine. The generated source and
// promise kernel are verified separately before this driver is run.
include "async-functions.dfy"
import opened LscAsync

method Drain(s: State) returns (t: State)
  decreases *
{
  t := s;
  while true
    decreases *
  {
    var i: nat := 0;
    while i < |t.jobs| && !Ready(t, i) { i := i + 1; }
    if i == |t.jobs| { return; }
    t := Resume(t, i);
  }
}

method Main()
  decreases *
{
  var s := Empty();
  var p: Promise;
  s, p := f2_eager_start(s, 4);
  expect Status(s, p) == Fulfilled(BigIntValue(4));
  expect |s.jobs| == 0;
  var other: Promise;
  s, other := f2_eager_start(s, 4);
  expect p.id != other.id;

  s := Empty();
  s, p := f3_yieldPlain_start(s, 4);
  expect Status(s, p).Pending?;
  expect |s.jobs| == 1;
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BigIntValue(4));

  s := Empty();
  s, p := f1_twice_start(s, 10);
  expect Status(s, p).Pending?;
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BigIntValue(12));
  s, p := f11_repeated_start(s, 10);
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BigIntValue(22));

  s := Empty();
  s, p := f4_recover_start(s);
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BigIntValue(7));
  s, p := f5_adoptWithoutCatch_start(s);
  expect |s.jobs| == 1 && s.jobs[0].adopting;
  s := Resume(s, 0);
  expect Status(s, p).Pending?;
  expect |s.jobs| == 1 && !s.jobs[0].adopting;
  s := Resume(s, 0);
  expect Status(s, p) == Rejected(BigIntValue(0));
  expect |s.jobs| == 0;

  s, p := f6_returnBeforeFinally_start(s);
  expect Status(s, p).Pending?;
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BigIntValue(1));
  s, p := f7_finallyOverrides_start(s);
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BigIntValue(5));
  s, p := f8_rethrow_start(s);
  s := Drain(s);
  expect Status(s, p) == Rejected(UndefinedValue);

  s := Empty();
  s, p := f10_shortCircuit_start(s, false);
  expect Status(s, p) == Fulfilled(BooleanValue(false));
  expect |s.outcomes| == 1 && |s.jobs| == 0;
  s, p := f10_shortCircuit_start(s, true);
  expect Status(s, p).Pending?;
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BooleanValue(true));

  s := Empty();
  var input: Promise;
  s, input := Allocate(s, (o: Outcome) => !o.Fulfilled? || o.value.BigIntValue?);
  var first: Promise;
  var second: Promise;
  s, first := f12_absolute_start(s, input);
  s, second := f12_absolute_start(s, input);
  expect first.id != second.id && first.id != input.id && second.id != input.id;
  expect !Ready(s, 0) && !Ready(s, 1);
  s := Settle(s, input, Fulfilled(BigIntValue(-3)));
  expect Ready(s, 0) && !Ready(s, 1);
  var ticket := s.jobs[0].ticket;
  s := Resume(s, 0);
  expect Status(s, first) == Fulfilled(BigIntValue(3));
  expect Status(s, second).Pending?;
  expect |s.jobs| == 1 && s.jobs[0].ticket != ticket;
  s := Drain(s);
  expect Status(s, second) == Fulfilled(BigIntValue(3));
  s := Settle(s, input, Fulfilled(BigIntValue(99)));
  expect Status(s, input) == Fulfilled(BigIntValue(-3));
  // Awaiting an already settled input still yields.
  s, p := f12_absolute_start(s, input);
  expect Status(s, p).Pending?;
  s := Drain(s);
  expect Status(s, p) == Fulfilled(BigIntValue(3));

  s := Empty();
  s, first := Allocate(s, (o: Outcome) => !o.Fulfilled? || o.value.UndefinedValue?);
  s, second := Allocate(s, (o: Outcome) => !o.Fulfilled? || o.value.UndefinedValue?);
  s, p := f13_cleanupBoth_start(s, first, second);
  expect Status(s, p).Pending?;
  s := Settle(s, first, Rejected(BigIntValue(0)));
  s := Drain(s);
  // A failed first cleanup does not skip waiting for the second cleanup.
  expect Status(s, p).Pending? && |s.jobs| == 1;
  s := Settle(s, second, Fulfilled(UndefinedValue));
  s := Drain(s);
  expect Status(s, p) == Rejected(BigIntValue(0));

  print "async runtime checks passed\n";
}
