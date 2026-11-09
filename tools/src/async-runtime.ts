/** The generated, verified promise kernel. Continuations are immutable frames.
 * Tickets and settlement times define FIFO jobs. Only Resume runs a queued job;
 * Advance executes the current synchronous stack, including eager async calls.
 */
export const ASYNC_RUNTIME = String.raw`
datatype Value = NumberValue(number: int) | BigIntValue(bigint: int)
  | BooleanValue(boolean: bool) | StringValue(text: string) | UndefinedValue
  | ReferenceValue(reference: int)
datatype Outcome = Pending | Fulfilled(value: Value) | Rejected(reason: Value)
datatype Promise = Promise(id: nat, ghost accepts: Outcome -> bool)

function Exact(o: Outcome): Outcome -> bool {
  (v: Outcome) => v == o
}
ghost predicate Accepted(p: Promise, o: Outcome) {
  !o.Pending? && p.accepts(o)
}
ghost predicate NewTo(p: Promise, known: set<Promise>) {
  forall q | q in known :: q.id != p.id
}

// The free variables of each closure are its saved locals. A source line marks
// each suspension. The supported source fragment cannot capture a mutable heap.
datatype Computation = Finished(outcome: Outcome)
  | Suspend(source: Promise, resume: Outcome -> Computation, line: nat)
  | Create(outcome: Outcome, created: Promise -> Computation)
  | Spawn(child: Computation, ghost post: Outcome -> bool,
          ghost roots: set<Promise>, created: Promise -> Computation)
  | Adopt(source: Promise)
  | Check(ghost condition: bool, next: Computation)
  | Fault

// Safety for ALL finite prefixes, not a bounded execution test. Keeping the
// universal predicate opaque lets each continuation be proved independently.
ghost predicate SafePrefix(c: Computation, post: Outcome -> bool, known: set<Promise>, fuel: nat)
  decreases fuel
{
  fuel == 0 || (
  match c
  case Finished(o) => !o.Pending? && post(o)
  case Suspend(p, k, _) => p in known &&
    (forall o :: Accepted(p, o) ==> SafePrefix(k(o), post, known, fuel - 1))
  case Create(o, k) => !o.Pending? &&
    (forall p: Promise :: p.accepts == Exact(o) && NewTo(p, known) ==>
      SafePrefix(k(p), post, known + {p}, fuel - 1))
  case Spawn(child, childPost, roots, k) => roots <= known && SafePrefix(child, childPost, roots, fuel - 1) &&
    (forall p: Promise :: p.accepts == childPost && NewTo(p, known) ==>
      SafePrefix(k(p), post, known + {p}, fuel - 1))
  case Adopt(p) => p in known && (forall o :: Accepted(p, o) ==> post(o))
  case Check(condition, next) => condition && SafePrefix(next, post, known, fuel - 1)
  case Fault => false)
}
opaque ghost predicate Correct(c: Computation, post: Outcome -> bool, known: set<Promise>) {
  forall fuel: nat :: SafePrefix(c, post, known, fuel)
}
ghost predicate SafetyStep(c: Computation, post: Outcome -> bool, known: set<Promise>) {
  match c
  case Finished(o) => !o.Pending? && post(o)
  case Suspend(p, k, _) => p in known &&
    (forall o :: Accepted(p, o) ==> Correct(k(o), post, known))
  case Create(o, k) => !o.Pending? &&
    (forall p: Promise :: p.accepts == Exact(o) && NewTo(p, known) ==>
      Correct(k(p), post, known + {p}))
  case Spawn(child, childPost, roots, k) => roots <= known && Correct(child, childPost, roots) &&
    (forall p: Promise :: p.accepts == childPost && NewTo(p, known) ==>
      Correct(k(p), post, known + {p}))
  case Adopt(p) => p in known && (forall o :: Accepted(p, o) ==> post(o))
  case Check(condition, next) => condition && Correct(next, post, known)
  case Fault => false
}

lemma FoldCorrect(c: Computation, post: Outcome -> bool, known: set<Promise>)
  requires SafetyStep(c, post, known)
  ensures Correct(c, post, known)
{
  reveal Correct();
  forall fuel: nat
    ensures SafePrefix(c, post, known, fuel)
  {
    if fuel > 0 {
      match c
      case Finished(_) =>
      case Adopt(_) =>
      case Fault =>
      case Check(_, next) =>
        assert SafePrefix(next, post, known, fuel - 1);
      case Suspend(p, k, _) =>
        forall o | Accepted(p, o)
          ensures SafePrefix(k(o), post, known, fuel - 1)
        { assert Correct(k(o), post, known); }
      case Create(o, k) =>
        forall p: Promise | p.accepts == Exact(o) && NewTo(p, known)
          ensures SafePrefix(k(p), post, known + {p}, fuel - 1)
        { assert Correct(k(p), post, known + {p}); }
      case Spawn(child, childPost, roots, k) =>
        assert SafePrefix(child, childPost, roots, fuel - 1);
        forall p: Promise | p.accepts == childPost && NewTo(p, known)
          ensures SafePrefix(k(p), post, known + {p}, fuel - 1)
        { assert Correct(k(p), post, known + {p}); }
    }
  }
}

lemma UnfoldCorrect(c: Computation, post: Outcome -> bool, known: set<Promise>)
  requires Correct(c, post, known)
  ensures SafetyStep(c, post, known)
{
  reveal Correct();
  assert SafePrefix(c, post, known, 1);
  match c
  case Finished(_) =>
  case Adopt(_) =>
  case Fault =>
  case Check(_, next) =>
    forall fuel: nat
      ensures SafePrefix(next, post, known, fuel)
    { assert SafePrefix(c, post, known, fuel + 1); }
  case Suspend(p, k, _) =>
    forall o | Accepted(p, o)
      ensures Correct(k(o), post, known)
    {
      forall fuel: nat
        ensures SafePrefix(k(o), post, known, fuel)
      { assert SafePrefix(c, post, known, fuel + 1); }
    }
  case Create(o, k) =>
    forall p: Promise | p.accepts == Exact(o) && NewTo(p, known)
      ensures Correct(k(p), post, known + {p})
    {
      forall fuel: nat
        ensures SafePrefix(k(p), post, known + {p}, fuel)
      { assert SafePrefix(c, post, known, fuel + 1); }
    }
  case Spawn(child, childPost, roots, k) =>
    forall fuel: nat
      ensures SafePrefix(child, childPost, roots, fuel)
    { assert SafePrefix(c, post, known, fuel + 1); }
    forall p: Promise | p.accepts == childPost && NewTo(p, known)
      ensures Correct(k(p), post, known + {p})
    {
      forall fuel: nat
        ensures SafePrefix(k(p), post, known + {p}, fuel)
      { assert SafePrefix(c, post, known, fuel + 1); }
    }
}

datatype Cell = Cell(outcome: Outcome, settledAt: nat)
datatype Job = Job(ticket: nat, output: Promise, source: Promise, adopting: bool,
  resume: Outcome -> Computation, line: nat, ghost known: set<Promise>)
datatype State = State(clock: nat, outcomes: seq<Cell>,
  ghost contracts: seq<Outcome -> bool>, jobs: seq<Job>)

function Empty(): State { State(0, [], [], []) }
ghost predicate Known(s: State, p: Promise) {
  p.id < |s.contracts| && p.accepts == s.contracts[p.id]
}
ghost predicate Knows(s: State, ps: set<Promise>) {
  forall p | p in ps :: Known(s, p)
}
function Status(s: State, p: Promise): Outcome
  requires p.id < |s.outcomes|
{ s.outcomes[p.id].outcome }
ghost function Outputs(s: State): set<nat> {
  set j | j in s.jobs :: j.output.id
}
ghost predicate JobCorrect(j: Job) {
  forall o :: Accepted(j.source, o) ==> Correct(j.resume(o), j.output.accepts, j.known)
}
ghost predicate Valid(s: State) {
  |s.outcomes| == |s.contracts| &&
  (forall i | 0 <= i < |s.outcomes| ::
    s.outcomes[i].settledAt <= s.clock &&
    (s.outcomes[i].outcome.Pending? || s.contracts[i](s.outcomes[i].outcome))) &&
  (forall j | j in s.jobs ::
    0 < j.ticket <= s.clock && Known(s, j.output) && Known(s, j.source) &&
    Knows(s, j.known) && NewTo(j.output, j.known) && Status(s, j.output).Pending? && JobCorrect(j)) &&
  (forall i, j | 0 <= i < j < |s.jobs| ::
    s.jobs[i].output.id != s.jobs[j].output.id && s.jobs[i].ticket < s.jobs[j].ticket)
}

function ReadyAt(s: State, j: Job): nat
  requires j.source.id < |s.outcomes| && (j.adopting || !Status(s, j.source).Pending?)
{
  var settled := s.outcomes[j.source.id].settledAt;
  if j.adopting || settled < j.ticket then j.ticket else settled
}
predicate Ready(s: State, i: nat) {
  i < |s.jobs| && s.jobs[i].source.id < |s.outcomes| && (s.jobs[i].adopting || !Status(s, s.jobs[i].source).Pending?) &&
  (forall k | 0 <= k < |s.jobs| && s.jobs[k].source.id < |s.outcomes| && (s.jobs[k].adopting || !Status(s, s.jobs[k].source).Pending?) ::
    ReadyAt(s, s.jobs[i]) < ReadyAt(s, s.jobs[k]) ||
    (ReadyAt(s, s.jobs[i]) == ReadyAt(s, s.jobs[k]) && s.jobs[i].ticket <= s.jobs[k].ticket))
}

// The host maps native promise identities to handles once. This operation also
// allocates async result handles; every allocation is distinct from all earlier
// handles, regardless of whether the async body contains an await.
method Allocate(s: State, ghost post: Outcome -> bool) returns (t: State, p: Promise)
  requires Valid(s)
  ensures Valid(t) && Known(t, p) && p.id == |s.outcomes| && p.accepts == post
  ensures t == State(s.clock, s.outcomes + [Cell(Pending, 0)], s.contracts + [post], s.jobs)
{
  p := Promise(|s.outcomes|, post);
  t := State(s.clock, s.outcomes + [Cell(Pending, 0)], s.contracts + [post], s.jobs);
}

method Settle(s: State, p: Promise, o: Outcome) returns (t: State)
  requires Valid(s) && Known(s, p) && p.id !in Outputs(s) && !o.Pending?
  requires Status(s, p).Pending? ==> Accepted(p, o)
  ensures Valid(t)
  ensures t.jobs == s.jobs && t.clock >= s.clock && t.contracts == s.contracts
  ensures |t.outcomes| == |s.outcomes|
  ensures Status(t, p) == (if Status(s, p).Pending? then o else Status(s, p))
  ensures forall i | 0 <= i < |s.outcomes| && i != p.id :: t.outcomes[i] == s.outcomes[i]
{
  if Status(s, p).Pending? {
    t := State(s.clock + 1, s.outcomes[p.id := Cell(o, s.clock + 1)], s.contracts, s.jobs);
  } else { t := s; }
}

method Register(s: State, output: Promise, source: Promise,
                k: Outcome -> Computation, line: nat, adopting: bool, ghost known: set<Promise>) returns (t: State)
  requires Valid(s) && Known(s, output) && Known(s, source) && Knows(s, known)
  requires Status(s, output).Pending? && output.id !in Outputs(s) && NewTo(output, known)
  requires forall o :: Accepted(source, o) ==> Correct(k(o), output.accepts, known)
  ensures Valid(t)
  ensures t.outcomes == s.outcomes && t.contracts == s.contracts && t.clock == s.clock + 1
  ensures t.jobs == s.jobs + [Job(t.clock, output, source, adopting, k, line, known)]
{
  t := State(s.clock + 1, s.outcomes, s.contracts,
    s.jobs + [Job(s.clock + 1, output, source, adopting, k, line, known)]);
}

method Start(s: State, c: Computation, ghost post: Outcome -> bool, ghost known: set<Promise>) returns (t: State, p: Promise)
  requires Valid(s) && Knows(s, known) && Correct(c, post, known)
  ensures Valid(t) && Known(t, p) && p.accepts == post && p.id == |s.outcomes|
  ensures s.clock <= t.clock
  ensures |s.jobs| <= |t.jobs| && t.jobs[..|s.jobs|] == s.jobs
  ensures |s.outcomes| < |t.outcomes| && t.outcomes[..|s.outcomes|] == s.outcomes
  ensures t.contracts[..|s.contracts|] == s.contracts
  ensures forall j | j in t.jobs[|s.jobs|..] :: |s.outcomes| <= j.output.id
  ensures forall j | j in t.jobs[|s.jobs|..] :: s.clock < j.ticket
  decreases *
{
  var initial;
  initial, p := Allocate(s, post);
  t := Advance(initial, p, c, known);
}

method Advance(s: State, output: Promise, c: Computation, ghost known: set<Promise>) returns (t: State)
  requires Valid(s) && Known(s, output) && Knows(s, known) && Status(s, output).Pending?
  requires output.id !in Outputs(s) && NewTo(output, known) && Correct(c, output.accepts, known)
  ensures Valid(t) && s.clock <= t.clock
  ensures |s.jobs| <= |t.jobs| && t.jobs[..|s.jobs|] == s.jobs
  ensures |s.outcomes| <= |t.outcomes| && t.contracts[..|s.contracts|] == s.contracts
  ensures forall i | 0 <= i < |s.outcomes| && i != output.id :: t.outcomes[i] == s.outcomes[i]
  ensures forall j | j in t.jobs[|s.jobs|..] :: j.output.id == output.id || |s.outcomes| <= j.output.id
  ensures forall j | j in t.jobs[|s.jobs|..] :: s.clock < j.ticket
  decreases *
{
  UnfoldCorrect(c, output.accepts, known);
  match c
  case Finished(o) =>
    t := Settle(s, output, o);
  case Suspend(source, k, line) =>
    t := Register(s, output, source, k, line, false, known);
  case Create(o, k) =>
    var withPromise, p := Allocate(s, Exact(o));
    var settled := Settle(withPromise, p, o);
    t := Advance(settled, output, k(p), known + {p});
  case Spawn(child, post, roots, k) =>
    var afterChild, p := Start(s, child, post, roots);
    t := Advance(afterChild, output, k(p), known + {p});
  case Adopt(source) =>
    // The result is fresh and cannot occur in its frame's known input handles.
    // Native adoption first queues the job that will attach the reaction.
    assert source.id != output.id;
    forall o | Accepted(source, o)
      ensures Correct(Finished(o), output.accepts, known)
    { FoldCorrect(Finished(o), output.accepts, known); }
    t := Register(s, output, source, (o: Outcome) => Finished(o), 0, true, known);
  case Check(condition, next) =>
    assert condition;
    t := Advance(s, output, next, known);
  case Fault =>
    assert false;
}

method Resume(s: State, index: nat) returns (t: State)
  requires Valid(s) && Ready(s, index)
  ensures Valid(t) && s.clock <= t.clock
  ensures |s.outcomes| <= |t.outcomes| && t.contracts[..|s.contracts|] == s.contracts
  ensures forall i | 0 <= i < |s.outcomes| && !s.outcomes[i].outcome.Pending? :: t.outcomes[i] == s.outcomes[i]
  ensures forall j | j in t.jobs :: j.ticket != s.jobs[index].ticket
  decreases *
{
  var j := s.jobs[index];
  var remaining := s.jobs[..index] + s.jobs[index + 1..];
  var popped := State(s.clock, s.outcomes, s.contracts, remaining);
  if j.adopting {
    // PromiseResolveThenableJob attaches the reaction in its own microtask.
    t := Register(popped, j.output, j.source, j.resume, j.line, false, j.known);
  } else {
    t := Advance(popped, j.output, j.resume(Status(s, j.source)), j.known);
  }
}
`;
