# DESIGN_ASYNC — Async translation and verification

**Status:** the initial result-oriented Dafny fragment is implemented; shared
effects, reentry, and application protocols below remain planned. See
[SPEC §4.5](SPEC.md#45-async-functions-dafny) for the supported source subset.

Verify ordinary async TypeScript in place. Separate three concerns: translating
execution, reasoning across suspension, and proving shared protocols.
Application invariants are needed only for properties that rely on them.

## 1. Translation: what executes

Translate each async function into a state machine containing its position,
live locals, and a fresh result promise. Execute the synchronous prefix
immediately; at await, save a continuation and arrange its later resumption.

For example:

```ts
async function increment(p: Promise<bigint>): Promise<bigint> {
  const x = await p
  return x + 1n
}
```

becomes, schematically:

```text
start(p):
    result = freshPromise()
    suspendOn(p, frame(result))
    return result

resume(frame, outcome):
    fulfilled(x): fulfill(frame.result, x + 1)
    rejected(e):  reject(frame.result, e)
```

This translation introduces no application invariant. It must preserve JavaScript
semantics: evaluate await operands before suspension; defer resumption even for
fulfilled promises or plain values such as `undefined`; preserve reference
identity and evaluation order; and route exceptions through the original handlers.
Returning another promise adopts its outcome while retaining a distinct result
promise. `return p` and `return await p` can behave differently under handlers.

The tool supplies a reusable model of promises and scheduling: permanent outcomes,
resolver behavior, adoption, and at-most-once execution of each registered
continuation. Queued continuations cannot interrupt a synchronous stack.
[ECMAScript Await](https://tc39.es/ecma262/2025/multipage/control-abstraction-objects.html#await)
and the related promise algorithms define the intended semantics.

## 2. Basic verification: what remains known

Ordinary contracts describe each sequential piece. Async contracts distinguish
the returned promise handle and synchronous-prefix effects from eventual
fulfillment or rejection. For `increment`, the output on fulfillment is the input
promise's value plus one; no shared-state invariant is needed.

At await, retain facts about unshared locals and memory proved protected from
interference. Forget facts about memory that other computations may modify.
A saved reference does not freeze its object, and TypeScript `const` or
`private` does not establish exclusive access.

Thus, after `const old = state.count; await ready;`, `old` is still known but
`state.count == old` may no longer hold. The function can reread and check the
state, prove that other operations cannot modify it, or use a shared invariant.
An invariant is not mandatory merely because a function uses shared state.

Calls also need effect information: a callback can synchronously reenter and
modify state before any await. Unknown effects require explicit external
contracts or conservative forgetting. Likewise, a postcondition true at promise
settlement can be used by a later waiter only when it remains valid until
resumption. Multiple awaiters can share completion facts; they cannot each
acquire exclusive ownership of the same resource.

The verifier must justify retained facts through alias/effect analysis,
ownership contracts, or checked interference summaries. The precise annotation
syntax and supported ownership discipline remain design work.

## 3. Shared protocols: when an invariant helps

Use an invariant when correctness depends on a relationship maintained by
overlapping operations. For a joining disposer, the relationship is that no
disposal result settles while its associated cleanup remains pending.
Preventing duplicate cleanup alone does not establish joining.

Declare the shared state and all operations that can affect it. Prove the
invariant initially and show that every participating operation preserves it
before suspension or exposing the state to another operation, including reentrant
callbacks. After suspension, assume the invariant while allowing other shared
facts to change. This rule is justified by preservation across all permitted
interference; declaring the invariant alone proves nothing.

For example, `this.pending = cleanup()` invokes cleanup before publishing its
result. Reentry during that call can observe an absent pending task, and
`await undefined` will succeed without waiting for cleanup. The compiler must
verify that ordering faithfully.

Coverage of writers through aliases must be checked, or explicitly bounded by
trusted external contracts. These protocol obligations are additional to the
basic async rules. The tool owns promise-model invariants; users supply
application invariants when their specifications need them.

## 4. Toolchain work and scope

Add an `async-lower` pass between typed resolution/narrowing and backend
transformation:

| Component | Change |
| --- | --- |
| Extraction and typed IR | Preserve async/await and exception control flow; represent promises separately from their values. |
| Async lowering | Build control-flow blocks, save live locals, and generate entry/resume operations and handler paths. |
| Verification encoding | Apply contracts and interference rules at await and effectful calls; add protocol obligations where declared. |
| Dafny backend | Emit the continuation methods and reusable promise model; map failures back to source locations. |

Promise handles must remain distinct even for async functions without await.
Narrowing must not preserve invalidated mutable-field facts. `autohavoc` and
optimizations must not erase suspension or reorder effects. Exception handling
requires an explicit encoding; general throws cannot become `assert false`.

Implement result-oriented async functions first, then shared-state effects and
reentry, then application protocols. Target Dafny and recognized native promises
initially; structural `Promise<T>` typing alone does not establish native behavior.
Reject unsupported constructs explicitly. Shared mutable captures, general
thenables, and generators require further work for existing Cordis compatibility.

Check translation against JavaScript traces and applicable ECMAScript tests.
Verify positive contracts and reject false ones, including stale-state claims
and premature completion. Translation correctness remains a compiler trust
boundary. These are safety claims; eventual completion requires additional
progress assumptions.

Keep TypeScript executable and the existing
`lsc check --backend=dafny` / `lsc regen --backend=dafny` workflow.
The compiler generates `.dfy.gen`; users add proofs to `.dfy` without maintaining
a second implementation.

## References

Start with de Vilhena–Pottier for promise contracts and Kamburjan et al. for
contracts under cooperative interference. Crowbar shows a tool implementation;
Sampaio et al. and ECMAScript address the JavaScript semantics to preserve.

- **de Vilhena and Pottier, [A Separation Logic for Effect
  Handlers](https://devilhena-paulo.github.io/files/separation-logic-effect-handlers.pdf),
  POPL 2021.** Read §6, especially Figure 11 (public promise contracts) and
  Figure 12 (internal invariants). Await obtains a persistent result assertion,
  reusable by multiple waiters. This is an Iris logic with ownership and ghost
  resources. The example omits exceptions and can resume immediately on an
  already fulfilled promise.
- **Kamburjan, Din, Hähnle, and Johnsen, [Asynchronous Cooperative Contracts
  for Cooperative Scheduling](https://ebjohnsen.org/publication/19-sefm/19-sefm.pdf),
  SEFM 2019.** A compositional contract logic for asynchronous calls and futures
  in ABS. Addresses the gaps between calling and executing, and between
  completing and consuming a result, plus interference at suspension. Its
  encapsulation assumptions need justification before adapting the rules to TS.
- **Kamburjan, Scaletta, and Rollshausen, [Crowbar: Behavioral Symbolic Execution
  for Deductive Verification of Active Objects](https://arxiv.org/abs/2102.10127),
  2021, revised 2022.** Concrete deductive verification of ABS using symbolic
  execution, specification-guided reasoning, and source-level counterexamples.
  Useful for studying a toolchain built around an explicit verification calculus;
  the language is ABS, with isolated object state.
- **Sampaio et al., [A Trusted Infrastructure for Symbolic Analysis of Event-Driven
  Web Applications](https://vtss.doc.ic.ac.uk/publications/Sampaio2020Trusted.pdf),
  ECOOP 2020.** See §§4.1–4.2 for JavaScript promises and async/await. Reference
  implementations and tests against applicable official suites provide a model
  for validating execution semantics. This addresses a different obligation from
  proving contracts inside an abstract promise model.
- **Ahrendt and Dylla, [A Verification System for Distributed Objects with
  Asynchronous Method Calls](https://people.mpi-inf.mpg.de/alumni/d5/2014/mdylla/publications/ICFEM09.pdf),
  ICFEM 2009.** See §4.3 for invariant reasoning at cooperative release points
  in Creol, using KeY. Earlier background for shared-state reasoning; object
  isolation is part of its setting.
- **Gray, Krishnamurthi, and Crichton, [A Design Space Exploration of
  Async/Await](https://arxiv.org/abs/2608.20677), 2026.** Semantic differences
  between languages, including eager calls and guaranteed suspension in
  JavaScript (§3.1). Useful when deciding which assumptions from another
  language's verification rules survive translation.
- **ECMAScript 2025: [Promise Objects](https://tc39.es/ecma262/2025/multipage/control-abstraction-objects.html#sec-promise-objects),
  [Await](https://tc39.es/ecma262/2025/multipage/control-abstraction-objects.html#await),
  and [PerformPromiseThen](https://tc39.es/ecma262/2025/multipage/control-abstraction-objects.html#sec-performpromisethen).**
  Normative execution semantics. In particular, settled means fulfilled or
  rejected; resolved can still mean pending when adopting another promise.
- **OpenJML, [Specifying Exceptions](https://www.openjml.org/tutorial/SpecifyingExceptions).**
  Precedent for normal `ensures` and exceptional `signals` postconditions.
  JML's typed exception syntax differs from JavaScript rejection values; these
  clauses alone supply no async interference discipline.
- **ABS language manual, [Await statement](https://abs-models.org/manual/statements.html#await-statement).**
  The executable guard `f?` observes whether a future contains a value or an
  exception, providing a concrete example of completion observations.
