# DESIGN_FSTAR — A backend for higher-order verification

**Status:** experimental backend implemented across the example suite; dependent callback domains and recursive combinator adapters remain proposed.
**Date:** September 26, 2026 (feasibility experiments September 25).
**Pre-implementation baseline:** LemmaScript 0.6.4, commit `097f18f`; Dafny 4.11.0; F* 2026.09.20 with its bundled Z3 4.13.3.

## Recommendation

The experimental F* backend supports **modular proofs about user-defined higher-order functions**, including functions returning functions, compositional postconditions and generic combinator laws. Callbacks with input-dependent contracts and recursive traversals whose callbacks operate on smaller subtrees remain proposed extensions. Dependent function types give these contracts a natural representation, while retaining SMT assistance. F*'s combination of dependent types and automated verification is described in its [language introduction](https://fstar-lang.org/tutorial/book/intro.html).

The case is weaker if the objective is simply supporting more uses of `map`, `filter`, or `reduce`. LemmaScript already handles those with Dafny, and several current restrictions belong to the shared frontend or lowering. Fixing those can benefit all backends. Keep Dafny as the default while measuring whether F* reduces proof work on a few representative higher-order programs. The existing Lean backend is also a relevant baseline: dependent types are not unique to F*, and LemmaScript already pays for Lean/Loom/Velvet integration.

The main uncertainty is proof ergonomics and engineering cost, rather than whether Dafny can express higher-order reasoning at all. Dafny has first-class functions, lambdas, and total, partial, and heap-reading arrow types (`->`, `-->`, `~>`). Its methods are not first-class function values. See the [Dafny reference on arrow types](https://dafny.org/latest/DafnyRef/DafnyRef).

## Implemented backend

`gen`, `gen-check`, `check`, and proof-preserving `regen --backend=fstar` work across all 76 top-level examples. `./regen-fstar.sh` builds the compiler, preserves proof additions, verifies each example, and fails on any failure or backend skip. The five `examples/fstar*.ts` programs exercise returned closures, general application, generic composition, map fusion, higher-order iteration and compiler correctness. Companions live in [examples/fstar/](examples/fstar/README.md), with readable source-based filenames; eleven working proofs contain additions to their generated baselines. See [SPEC_FSTAR.md](SPEC_FSTAR.md) for commands and precise model boundaries.

The emitter now consumes the shared lowered IR through `transformModuleFstar`, with a small F*-specific mode that preserves expression types, general application and the specification result binder. Dafny and Lean retain their existing lowering. [fstar-source.ts](tools/src/fstar-source.ts) rejects constructs whose behavior extraction would erase, including mutation of captured state and reference-identity comparisons. Local updates become fresh values; loops become recursive continuations with invariant preconditions, enclosing postconditions and checked termination measures. Classes use explicit record state and result/state pairs.

The packaged [LS.Runtime.fst](tools/fstar/LS.Runtime.fst) supplies proved adapters for finite sequences, UTF-16 strings, arrays, arithmetic, maps and sets. Arrays use `FStar.Sequence`; string keys use a proved list encoding because finite-map keys require decidable equality. Specifications and higher-order arrows use F* `Ghost`/`GTot`, allowing mathematical sequence and finite-set operations. This is a verification model; TypeScript still runs the program.

Explicit source `extern`, `impure`, `havoc`, `autohavoc` and `assume` annotations remain visible trust boundaries. Impure evaluations receive call-site and iteration traces to avoid identifying distinct results. Unicode case conversion is a deterministic uninterpreted library abstraction with no assumed result properties. No proof additions may introduce new assumptions or admissions.

[proof-files.ts](tools/src/proof-files.ts) shares additions-only comparison and recovery-aware three-way merging with Dafny. [fstar-commands.ts](tools/src/fstar-commands.ts) verifies the runtime explicitly in an isolated directory before checking the working proof against that fresh checked dependency. Merely importing an unchecked F* module can load it laxly, so checking only the client is insufficient. The pinned CI job runs positive and negative tests, verifies every example, and checks artifact drift.

The demonstrated higher-order benefits are direct composition of function postconditions and returned-closure contracts. Supporting the existing imperative examples establishes useful coverage; it does not establish that F* universally reduces proof work compared with Dafny. The Map/Set and counting proofs still need explicit quantifier guidance and mathematical helper lemmas.

[fstarCompiler.ts](examples/fstarCompiler.ts) compiles expression trees into continuation-passing closures and proves `compile(e)(env, k) === k(evaluate(e, env))` for every environment and continuation. Recursive compilation composes these higher-order contracts through constant folding, zero multiplication and lexical binding. Its working proof keeps the compiler opaque to SMT callers and normalizes the concrete nested-shadowing demo; the general semantic-preservation theorem verifies automatically. Negative tests reject a compiler that drops the continuation or forgets a binding.

## Baseline code, before this prototype

This section records the pre-implementation baseline above. Its pipeline was `extract → resolve → narrow → autohavoc → transform → peephole → emit`. The first three stages were reusable; the later stages contained backend decisions. The table describes the changes that were needed, rather than the current F* implementation.

| Area | Observation | Consequence for F* |
| --- | --- | --- |
| [types.ts](tools/src/types.ts), [typedir.ts](tools/src/typedir.ts) | `Ty` already has `fn { params: Ty[]; result: Ty }`; TS function type nodes are parsed structurally. | Basic function values need no new TS syntax. Callback contracts, parameter binders, and effects are absent from this type representation. |
| [rawir.ts](tools/src/rawir.ts), [typedir.ts](tools/src/typedir.ts), [ir.ts](tools/src/ir.ts) | Raw and Typed IR calls have an expression-valued callee. Final IR `app` has only `fn: string`. | Preserve general application through lowering; a third pretty-printer alone cannot fix nested calls. |
| [resolve.ts](tools/src/resolve.ts) | `classifyCall` treats function-typed local variables as pure. Purity detection is primarily syntactic plus a same-file call graph; impure extern calls are rejected in lambdas. | This is not a general closure/effect analysis. The new backend needs an explicit supported-fragment check, including nested callbacks and captures. |
| [transform.ts](tools/src/transform.ts) | `flattenLambdaBody` handles immutable lets, conditionals, matches, and returns. Remaining statement bodies survive. Calls other than variables or field calls are rejected. | Pure block lambdas already work in many cases. Loops and assignments need further lowering; returned-function application needs a general `apply` node. |
| [dafny-emit.ts](tools/src/dafny-emit.ts) | Function types always become total `->` arrows. `.map` uses an inlined sequence comprehension; `.filter`, `.every`, and `.reduce` use standard-library functions. | Current callback types cannot describe a domain-restricted function. The `.map` specialization is deliberate: it exposes the smaller element to termination checking. |
| [dafny-emit.ts](tools/src/dafny-emit.ts), `case "def"` | Pure-function postconditions become companion `_ensures` lemmas; they are not emitted on the function itself. | This is an emitter/workflow choice, not a Dafny limitation. Hand-added function `ensures` already allow caller composition, as documented in [AGENTS.md](AGENTS.md). |
| [builtins.ts](tools/src/builtins.ts), [lsc.ts](tools/src/lsc.ts) | Builtins had HOF shape metadata; CLI dispatch and backend types only admitted `dafny` and `lean`. | Reuse builtin identities, but add real capability checks and explicit F* dispatch. The baseline CLI fell through to Lean after the Dafny branch. |

The existing examples are useful starting points: [hof.ts](examples/hof.ts) covers array callbacks and an immutable capture, [lambdaFlatten.ts](examples/lambdaFlatten.ts) and [switchLambda.ts](examples/switchLambda.ts) cover block-to-expression lowering, and [filterMap.ts](examples/filterMap.ts) covers optional callback results. [SPEC.md §3.7](SPEC.md#37-higher-order-functions-and-lambdas) explains these translations.

In particular, this existing annotation language already expresses a useful higher-order contract:

```typescript
export function twice(f: (x: number) => number, x: number): number {
  //@ requires forall(y: int, f(y) >= y)
  //@ ensures \result >= x
  return f(f(x));
}
```

A temporary probe through the baseline source CLI and Dafny verified this with **2 verified, 0 errors**, without proof additions. That is a baseline for evaluating F* on larger examples, rather than evidence of a missing Dafny capability.

## Where F* could improve the experience

### Contracts travel with function values

In F*, the callback's result can mention its argument directly:

```fstar
type step = x:int -> Tot (y:int{y >= x})

let twice (f:step) (x:int) : Tot (y:int{y >= x}) =
  f (f x)
```

Every call to `f` exposes its guarantee through its type. A caller supplying `fun x -> x - 1` fails to meet the callback type. A domain restriction can likewise be represented as `x:int{x >= 0} -> Tot int`; this function is total on its specified domain, not on all integers. F* checks termination separately from purity. See [total computation types](https://fstar-lang.org/tutorial/book/part4/part4_computation_types_and_tot.html).

The implemented compiler preserves existing annotations without adding callback syntax. Omitting generated name prefixes, the TS `twice` above becomes:

```fstar
let twice (f:int -> GTot int) (x:int)
  : Ghost int
    (requires (forall (y:int). f y >= y))
    (ensures (fun r -> r >= x)) =
  f (f x)
```

`Ghost` carries the function's pre/postcondition at its definition, so callers receive the verified postcondition directly. `Ghost`/`GTot` accommodate the mathematical sequence and collection libraries used by the verification model; TypeScript remains executable. The earlier standalone experiments used `Pure`/`Tot`, which also carry compositional contracts; see [F*'s primitive effect refinements](https://fstar-lang.org/tutorial/book/part4/part4_pure.html).

Reusable, explicitly domain-restricted callback contracts remain a proposed shared language feature. They need structured contract metadata containing named input binders, a result binder, pre/postcondition ASTs, and an effect/totality requirement, preserved through resolution, aliases, and application. Their TS annotation syntax is still undecided; `//@ type` currently parses TS-shaped types and cannot simply accept arbitrary F* refinements. A TS type `(x: number) => number` alone establishes neither purity nor a mathematical callback contract.

Verified callers must discharge callback contracts and purity requirements; an unverified TS caller remains an explicit boundary assumption. Ordinary runtime shape checks cannot establish a universally quantified callback guarantee.

### Generic combinator proofs

F* can quantify over types and functions directly. The following complete module verified with the pinned release; it proves a law for arbitrary pure total callbacks rather than testing particular lambdas:

```fstar
module Fusion

let rec map (#a:Type) (#b:Type) (f:a -> Tot b) (xs:list a)
  : Tot (list b) (decreases xs) =
  match xs with
  | [] -> []
  | x::tl -> f x :: map f tl

let rec map_fusion (#a:Type) (#b:Type) (#c:Type)
  (f:a -> Tot b) (g:b -> Tot c) (xs:list a)
  : Lemma (map g (map f xs) == map (fun x -> g (f x)) xs)
    (decreases xs) =
  match xs with
  | [] -> ()
  | _::tl -> map_fusion f g tl
```

The working [fstarArrays.fst](examples/fstar/fstarArrays.fst) now proves map fusion for the generated sequence model using a handwritten induction. Filter composition and fold invariant preservation remain further experiments. F*'s [polymorphism chapter](https://fstar-lang.org/tutorial/book/part1/part1_polymorphism.html) covers the type arguments and higher-order application used here.

### Recursive callbacks need stronger combinators

Changing provers does not automatically fix recursive calls hidden inside `map`. This standalone F* program **failed** termination checking:

```fstar
module Walk

type tree =
  | Node : children:list tree -> tree

let rec walk (t:tree) : Tot tree (decreases t) =
  match t with
  | Node children -> Node (FStar.List.Tot.map walk children)
```

The ordinary library `map` expects a callback on every element of the element type. Inside `walk`, recursive calls are available only on smaller trees. F* cannot establish that restriction for an arbitrary argument supplied through this signature.

This alternative **verified** with `--report_assumes error`:

```fstar
module WalkBelow

type tree =
  | Node : children:list tree -> tree

let rec map_below (parent:tree) (xs:list tree{xs << parent})
  (f:(x:tree{x << parent} -> Tot tree))
  : Tot (list tree) (decreases xs) =
  match xs with
  | [] -> []
  | x::tl -> f x :: map_below parent tl f

let rec walk (t:tree) : Tot tree (decreases t) =
  match t with
  | Node children -> Node (map_below t children (fun child -> walk child))
```

Here `<<` is F*'s well-founded ordering. The helper exposes the fact needed at the recursive call through the callback's domain. The mechanism is described in [F*'s termination chapter](https://fstar-lang.org/tutorial/book/part1/part1_termination.html).

This is a concrete reason to investigate F*: a verified library of domain-aware combinators might replace repeated emitter specialization. It is also a design obligation. A production helper needs an ordinary-map equivalence theorem, and lowering must prove each domain restriction. Trees containing sequences, mutually recursive types, or user-supplied numeric measures may need different helpers. The experiment establishes one useful encoding, not a general termination solution.

### What this will not establish by itself

F* still sends higher-order reasoning through an encoding to a first-order SMT solver. Quantifiers, unfolding, nonlinear arithmetic, and proof stability remain concerns; there is no evidence here that it will consistently outperform Dafny. See [how F* uses Z3](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html).

Pointwise equality of mathematical functions also differs from JavaScript function reference identity. Function `===`/`!==` is rejected. Proof-level extensionality can be introduced separately, with explicit library assumptions where applicable.

Mutable captures, aliasing, exceptions, nondeterministic callbacks, and async scheduling require a state/effect model. An F* arrow is not such a model. These remain outside the backend; the implemented local updates use value semantics. Current F* includes Pulse for imperative verification; older instructions about Low* and “Dijkstra monads for free” need care because the [April 2026 release](https://github.com/FStarLang/FStar/releases/tag/v2026.04.17) removed those components. Supporting effectful callbacks is a separate project.

## Architecture and remaining roadmap

The implemented pipeline is:

```text
TS → extract → source capability check → resolve → narrow → autohavoc
   → transformModuleFstar → fstar-emit → isolated runtime + proof verification
```

`transformModuleFstar` reuses the shared value-model rewrites while retaining a native postcondition result binder and expression-valued application. In particular, F* must not inherit Dafny's substitution of a function call for `\result` in companion lemmas. The optional expression type metadata is attached only on this path. The emitter orders declarations by dependency and checks self recursion; mutual recursion is still rejected.

The runtime preserves sequence order, UTF-16 indexing, left-fold direction, signed division/remainder and the existing idealized number model. Sorting requires a total preorder and proves membership, length and multiplicity preservation. Arrays and mutable collections use values rather than shared heap references. Source trust annotations are retained explicitly; unsupported callback effects cannot be hidden behind a pure F* arrow.

Further work should focus on three measurable improvements: carry input-dependent callback contracts in the typed IR; prove and lower domain-aware recursive combinators such as `map_below`; and design proof insertion points that enforce preservation of program behavior more strongly than an additions-only textual check. Shared heap effects, async scheduling, imported checked project modules and module-state mutation require separate designs.

### Proof artifacts and regeneration

The prototype uses the familiar Dafny-style pair. TS remains the source of truth for the program; the working `.fst` owns proof additions. For example, `examples/fstarClosures.ts` produces:

| Artifact | Ownership |
| --- | --- |
| `examples/fstar/fstarClosures.fst.gen` | Generated baseline; always regeneratable |
| `examples/fstar/fstarClosures.fst` | Generated program plus hand-written proof additions; verified by F* |
| `examples/fstar/fstarClosures.fst.base`, `.fst.merged` | Temporary merge/recovery state |

Companions use the source basename inside a sibling `fstar/` directory. Internal module names combine an escaped basename and a digest of the path relative to the config/tsconfig directory, falling back to the source directory. This resolves case/punctuation collisions and survives checkout relocation with the same layout. The verifier copies each working proof to a temporary filename matching its module declaration, keeping opaque filenames out of the repository. Commands migrate the old module-named companions together with their baselines and recovery state, refusing to combine two existing sets. The existing `proof-dir` option remains Dafny-only.

`gen` replaces only the baseline and seeds a missing working file. `check` enforces additions-only and verifies the working module. `regen` merges against the correct old generation, preserves proof additions, and retains recovery state on failure. Carry over the documented Dafny conflict and failed-verification anchor rules. Never recreate a working proof by deleting it.

F* often needs a ghost lemma invocation or assertion before the expression whose type is being checked. This is why the backend currently uses a pair, even when automatic verification leaves the two files identical. Moving companions into `fstar/` improves the layout but retains this duplication. A Lean-like split into immutable definitions and separate proofs is attractive for external theorems, but it does not by itself discharge refinements inside generated definitions. It would need a designed, acyclic mechanism for proof hooks.

Proof additions may supply ghost definitions, checked assertions, and lemma calls; they must preserve the program and declared contracts. An additions-only text check is an editing discipline, not a proof that arbitrary inserted F* expressions preserve behavior. Constrained proof insertion points and checking their ghost-only nature are a hardening task before broader adoption.

An `.fsti` is an interface, not a proof file. A signature with no checked implementation is an assumption; verifying only an interface or a client is insufficient. `check` must verify implementations for all project modules on which it relies and keep external axioms explicit. See [F* interfaces](https://fstar-lang.org/tutorial/book/part3/part3_interfaces.html) and [module abstraction](https://fstar-lang.org/tutorial/book/part3/part3.html).

### Verification command contract

After `npm run build`, these commands run from this checkout:

```sh
node tools/dist/lsc.js gen   --backend=fstar examples/fstarClosures.ts
node tools/dist/lsc.js check --backend=fstar examples/fstarClosures.ts
node tools/dist/lsc.js regen --backend=fstar examples/fstarClosures.ts
```

The command runner invokes `fstar.exe` (or `FSTAR_EXE`) with an argument array, copying the working module into a fresh directory and forcing verification. Missing binaries fail. The backend rejects `.fsti` companions and does not reuse project caches or unchecked dependencies; it checks the packaged runtime explicitly and relies on the installed standard library. Any future project caching must bind source, dependencies, options, and toolchain versions. A successful `gen` or cached parse must never be reported as a verification success.

The runner rejects verification-bypass flags, new proof assumptions, admissions and source option directives; it permits only the resource flags listed in [SPEC_FSTAR.md](SPEC_FSTAR.md#verification-and-trust-boundary). Verification uses `--report_assumes error`, except that generated source `assume` statements require `warn` so their explicit trust is reported. Generated extern declarations remain part of the source model. Bundled foundational libraries remain part of the chosen trust boundary.

`--time-limit` is a process deadline applied separately to runtime verification and working-proof verification. F*'s `--z3rlimit` is a resource budget, not a seconds timeout. Nonzero exit status fails verification even if diagnostics include `Verified module`: the initial negative probe printed `Verified module: Bad` despite exiting 1 with an error.

## Feasibility experiments and implementation gates

These initial feasibility experiments ran in a temporary directory, before backend implementation; existing source and proof artifacts were not changed by those probes. The F* binary was unpacked there without changing PATH, shell startup files, or the OPAM switch. The installed Homebrew `z3` was not used for F*.

| Experiment | Observed result |
| --- | --- |
| Baseline Dafny CLI: TS `twice` with quantified callback precondition | 2 verified, 0 errors |
| Baseline Dafny CLI: `makeAdder(1)(2)` | Generation failed: `Unsupported call expression: call` |
| Baseline Dafny CLI: `.map` callback with a local accumulation loop | Generation failed: `Unsupported: multi-statement lambda in Dafny` |
| F*: refined `twice`, returned immutable closure, domain-restricted callback | Verified |
| F*: `Pure` version of `twice` and a caller using its guarantee | Verified, including `--report_assumes error` |
| F*: generic map-fusion lemma | Verified |
| F*: decrementing callback supplied to `step` | Rejected: cannot prove `x - 1 >= x` |
| F*: recursive tree walker through ordinary `FStar.List.Tot.map` | Rejected: cannot prove the recursive argument is smaller |
| F*: tree walker through `map_below` | Verified, including `--report_assumes error` |

These historical probes motivated the implementation. They are not a semantic-equivalence proof or performance comparison; the implemented coverage is described above.

1. **Pure vertical slice — implemented.** Numeric HOFs, composition, immutable captures, shadowing and returned closures have positive and negative verification tests. Existing annotations are preserved; mutable captures are rejected. Differential comparison with TS execution remains future work.
2. **Dependent callback contracts — proposed.** Direct function and returned-closure postconditions compose today. Named callback types with restricted input domains and dependent output relations still need shared metadata and annotation syntax, along with failing-caller and failing-callback tests.
3. **Recursive combinators — proposed.** Generate a tree traversal through a domain-aware adapter without modifying the TS algorithm. Prove the adapter's map equivalence and termination obligations. Compare proof additions against Dafny comprehensions and an improved Dafny encoding with direct function postconditions.
4. **Proof workflow — implemented, ergonomics still to measure.** F* and shared artifact tests cover proof preservation, regeneration/recovery, migration, verifier failures, false specs and proof-policy rejection. CI checks the existing backends and all F* examples. Comparative proof size, manual steps and verification stability still need a systematic benchmark.
5. **Broader value-model coverage — implemented.** Local mutable loops and explicit class state are functionalized, and all 76 examples verify. Aliasing, shared heap effects and scheduling remain separate work. Broader syntax coverage does not by itself establish better higher-order proof ergonomics.

Proceed beyond the prototype if the callback-domain, composition, and traversal cases show a repeatable improvement in proof work. If the gains mostly come from general application support or better Dafny postcondition emission, land those shared/backend fixes first and reconsider the third backend.

## Local setup walkthrough: this Mac

The inspected host is macOS on `arm64`. During the initial audit, OPAM and OCaml were present but `fstar.exe` was not on PATH. F* has since been installed using the official release installer and reports 2026.09.20; the implementation examples verify with it. The Homebrew Z3 is 5.1.0; F* uses its bundled Z3 4.13.3 instead. If `fstar.exe --version` already works, skip installation and use the compiler commands above.

Use the native binary package first. The official [v2026.09.20 release](https://github.com/FStarLang/FStar/releases/tag/v2026.09.20) has a `Darwin-arm64` archive, and the [installation guide](https://github.com/FStarLang/FStar/blob/master/INSTALL.md) recommends binary packages with bundled solvers. OCaml compilation and an OPAM switch are unnecessary for this verification-only experiment.

### 1. Install a pinned release

Run these commands in Terminal. The versioned destination keeps this installation distinct from other F* versions. The installer replaces an existing destination, so use this path only for that release installation.

```sh
fstar_setup_dir=$(mktemp -d)
curl -fsSL \
  https://raw.githubusercontent.com/FStarLang/FStar/v2026.09.20/.scripts/install-fstar.sh \
  -o "$fstar_setup_dir/install-fstar.sh"
bash "$fstar_setup_dir/install-fstar.sh" --help
bash "$fstar_setup_dir/install-fstar.sh" \
  --release --version v2026.09.20 \
  --dest "$HOME/.local/fstar-v2026.09.20" --no-link
export PATH="$HOME/.local/fstar-v2026.09.20/bin:$PATH"
```

The flags were checked against the [version-pinned installer](https://github.com/FStarLang/FStar/blob/v2026.09.20/.scripts/install-fstar.sh). It detects the OS/architecture and downloads the release archive. No `sudo` or Rosetta is needed for the native package. To make F* available in future zsh terminals, add the final `export PATH=...` line to `~/.zshrc` once.

### 2. Check the executable and solver

```sh
command -v fstar.exe
fstar.exe --version
fstar.exe --locate_z3 4.13.3
```

Expect F* `2026.09.20`, `Darwin_arm64`, and a solver path inside this installation. The `.exe` suffix is also used on macOS. Let F* select its bundled Z3; do not substitute the unrelated `z3` on PATH. The downloaded release and bundled solver were successfully executed on this host.

### 3. Verify a higher-order example

The following creates a scratch file outside the repository:

```sh
fstar_try_dir=$(mktemp -d)
cd "$fstar_try_dir"
cat > Smoke.fst <<'EOF'
module Smoke

type step = x:int -> Tot (y:int{y >= x})

let twice (f:step) (x:int) : Tot (y:int{y >= x}) =
  f (f x)

let demo : y:int{y >= 10} = twice (fun x -> x + 1) 10

let make_adder (n:int) : Tot (x:int -> Tot (y:int{y == x + n})) =
  fun x -> x + n

let closure_demo : y:int{y == 3} = (make_adder 1) 2

let apply_nat (f:nat -> Tot nat) (x:nat) : Tot nat = f x
EOF
fstar.exe --report_assumes error Smoke.fst
```

Expected final line: `All verification conditions discharged successfully`, with exit status 0. `Tot` means pure and terminating; `{...}` constrains a value; the returned function from `make_adder` carries its own contract. This file was checked during the design investigation.

### 4. Confirm that a false contract fails

```sh
sed -e 's/^module Smoke$/module Bad/' \
    -e 's/x + 1/x - 1/' Smoke.fst > Bad.fst
fstar.exe --report_assumes error Bad.fst
```

Expect a nonzero exit and a failed obligation equivalent to `x - 1 >= x`. This checks that verification is actually running. Then save the `Fusion` or `WalkBelow` module above in a correspondingly named `.fst` file and verify it the same way to explore induction or recursive callbacks.

### 5. Verify the generated LemmaScript examples

Return to the LemmaScript checkout, run `npm run build`, then `node tools/dist/lsc.js check --backend=fstar examples/fstarClosures.ts`. Repeat for `fstarComposition.ts`, `fstarArrays.ts`, and `fstarIteration.ts`, or run `./regen-fstar.sh` to build, regenerate and verify all examples. Companions live in `examples/fstar/`; verification through `lsc` handles their internal module filenames. The standalone domain-restricted callback and tree examples above go beyond the implemented subset. After edits under `tools/`, rebuild before using the compiled CLI.

If setup fails, first check that `command -v fstar.exe` selects the intended installation, that `uname -m` is `arm64`, and that `--locate_z3 4.13.3` locates the bundled solver. For a source build or OPAM installation, follow the current [upstream installation instructions](https://github.com/FStarLang/FStar/blob/master/INSTALL.md); compiler constraints and solver requirements vary by release. Pin the same working release in CI before comparing proof behavior.
