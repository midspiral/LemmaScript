# DESIGN_RUN_LOG — Counting what verification caught

**Status:** recording of `check` and `regen` runs is implemented (§1–§2). `lsc runs`, claimcheck records, labels and reports are not yet built. A stopgap wrapper on the `lemmascript-catch-log` branch of lemmascript-skills confirmed the Dafny CSV approach against `lsc` 0.6.1, passing the flag through `--extra-flags`; the implementation uses the text format instead (§2).
**Date:** September 2026

## Goal

When an agent writes LemmaScript code and proofs, the prover and claimcheck reject things along the way. Some rejections are real bugs in the TypeScript, some are specs that said the wrong thing, and many are ordinary proof work. We want honest counts of each, reported periodically over the life of a project.

Asking the agent to keep a tally at the end of a session does not give honest counts. The agent's memory of the session is incomplete, and it tends to call every failed proof attempt a "bug caught". This design has `lsc` record every verification run itself, together with a snapshot of the source. A catch is then a fact derived from the record: something failed, and a later run passed.

Labeling a catch as a code bug or a spec bug happens afterward, at report time. A reporting skill reads the log, looks at what changed in the source between the failing and the passing run, and labels each catch from that diff. The agent doing the work has no extra duties while it works.

In this document a **catch** is a fact about the history, not a bug: a member that failed in one run and passed in a later one. Most catches are ordinary proof work; only some are bugs, and §4 and §5 sort them.

## Requirements

1. **Mechanical first.** A catch exists only if the log shows a failure followed by a pass. 
2. **Always on.** Every `lsc check`, `lsc regen`, and `lsc claimcheck` on a file is recorded, whoever runs it: an agent, a person, or CI. No wrapper, skill rule, or hook is needed for logging.
3. **No change to what the user sees.** Logging does not alter `lsc` output, exit codes, or generated files. Dafny's output still streams to the terminal while it runs.
4. **Invisible to git.** The log directory ignores itself, so it never shows up in `git status` and needs no `.gitignore` edit.
5. **Code and proof are kept apart.** The record shows whether the fix touched the `.ts` (the program or its spec) or only the `.dfy` (the proof). The two are reported separately.
6. **Labels are made after the fact, from evidence.** The log keeps enough to label a catch later without the working agent's memory: the source before and after the fix, and the error that preceded it (error text is not yet recorded; see §2).
7. **Claimcheck is counted the same way, and is not modified.** `lsc` reads the report file that claimcheck already writes.
8. **Logging never fails a run.** A logging error (unwritable directory, full disk) is swallowed; output and exit codes are unchanged.

## 1. Where the log lives

Logging is on by default. A project turns it off with a config-only entry in the registry (see DESIGN_CONFIG.md §2):

```json
{
  "run-log": false
}
```

`LSC_RUN_LOG=false` turns it off for a single run; like `lemmascript.json`, the variable accepts only `true` or `false`.

`run-log` is config-only, not a `//@ option`: a file that could switch off its own logging would let an agent hide the failures the log exists to count.

The log lives in `.lemmascript/` in the directory that holds the selected `lemmascript.json`. Without a config file, it goes beside the nearest `LemmaScript-files.txt` (so a project's manifest anchors the log even when the project sits inside a larger repository), else in the git repository root, else in the current working directory; in that last case the run history depends on where `lsc` is run from, so add a `lemmascript.json` or `LemmaScript-files.txt` to anchor it. When `lsc` creates the directory, it writes `.lemmascript/.gitignore` containing `*`, so git ignores the whole directory without any change to the project's own `.gitignore`.

```
.lemmascript/
  .gitignore        contains "*"
  runs.jsonl        one record per run, plus label and report records
  blobs/<hash>.ts   source snapshots, one file per distinct version
  reports/          dated reports, one file per `lsc runs report` (§6)
```

## 2. What `lsc check` and `lsc regen` record

`dafnyVerify` (`tools/src/dafny-commands.ts`) gains one extra Dafny argument when logging is on:

```
--log-format text;LogFileName=<tmp>/verify.txt
```

Dafny writes one `Results for <member> (<check>)` block per verified member, each with an `Overall outcome`, and its terminal output is unchanged. `lsc` keeps Dafny's stdio inherited. The CSV format was rejected because it always prints an extra `Results File:` line, which `lsc` could only remove by piping Dafny's output, and streaming piped output would make the whole check/regen path asynchronous. The cost is that records do not yet carry Dafny's error messages.

The helper that detects how the run ended appends one record: `dafnyCheckDiff` for `diff`, `dafnyVerify` for `ok`, `verify` and `resolve`, and `dafnyRegen` for `conflict` and `--no-verify` runs.

```json
{"v":1,"type":"verify","id":"6f1c…","ts":"2026-10-05T21:14:02Z",
 "cmd":"check","file":"src/domain.ts","stage":"verify","exit":1,"partial":false,
 "failed":["applyDiscount_ensures"],"passed":["clamp","clamp_ensures","applyDiscount"],
 "tsHash":"9c1e04b2d7aa","dfyHash":"41d0f93be812",
 "lsc":"0.6.4"}
```

- **`stage`** tells where the run stopped. `diff` means the additions-only check failed, so Dafny never ran. `resolve` means Dafny wrote no member results (a parse or resolution error, or `lsc` refused the proof before running Dafny). If Dafny is not installed, nothing was verified and the run is not recorded. `conflict` means a `regen` merge conflicted. `verify` means Dafny ran and reported failures. `ok` means everything that ran passed.
- **`failed` / `passed`** are member names. A member that fails either check appears once, in `failed`.
- **`partial`** is `true` when the run did not report on every member: Dafny never ran or wrote no results, `regen --no-verify`, or a `--filter-symbol` / `--filter-position` flag. Only a non-partial run can make a member disappear (§4).
- **`exit`** is the exit code `lsc` ends with. **`v`** is the record schema version; **`id`** is a random UUID; `lsc` (the version) gives context; fields such as the git commit or whether the run came from CI can be added in a later schema version if records leave the machine.
- **`tsHash` / `dfyHash`** are the first 12 hex characters of the SHA-256 of the source `.ts` and of the proof `.dfy`. The `.ts` is hashed when the run starts. The `.dfy` is hashed when the run ends, because `check` may create it and `regen` may merge into it.

**Snapshots.** On every run, `lsc` copies the `.ts` to `.lemmascript/blobs/<tsHash>.ts` unless that file already exists. Most runs during proof work leave the `.ts` unchanged, so they add nothing. The `.dfy` is not snapshotted, because labeling only needs to see what changed in the program and its spec.

## 3. What `lsc claimcheck` records

Claimcheck already writes `<name>.guarantees.json` next to the source, or under `--out`. Each entry in it has a function name, the contract text (`requirement`), the formal `spec`, a `status` of `confirmed`, `disputed`, or `unchecked`, and, for disputes, a `discrepancy` and a `backTranslation`.

After claimcheck finishes, `lsc` reads that file, snapshots the `.ts`, and appends one record. In the single-file branch this happens after the dynamic `import` resolves; in the batch branch it happens after each `execFileSync`. `lsc` works out the report path from the same `--out` argument it forwards.

```json
{"type":"claimcheck","id":"r_7f3b","ts":"2026-09-30T21:20:44Z",
 "file":"src/domain.ts","tsHash":"9c1e04b2d7aa",
 "results":[
   {"fn":"applyDiscount","status":"disputed","contractHash":"5b21","specHash":"e0c7",
    "weakeningType":"missing-bound","discrepancy":"The spec bounds the result below but not above."}
 ]}
```

`specHash` covers `requires` and `ensures` together, since a dispute can be resolved by changing either. Hashing the contract text and the spec separately lets the report tell, without any judgment, whether a dispute was resolved by changing the prose or by changing the spec.

## 4. From runs to catches

A new subcommand reads the log and derives the catches:

```sh
npx lsc runs                 # everything not yet covered by a report
npx lsc runs --all           # the whole log, ignoring past reports
npx lsc runs --json          # machine-readable, with labeling evidence (combines with --all)
npx lsc runs report          # write a dated report of everything not yet reported (§6)
```

There are no sessions. `lsc runs` always derives catches from the whole log, because a failure can be fixed days after it happened, and then shows only what falls after the most recent report.

**A verify catch** is a member `M` in file `F` that appears in `failed` in some run, and in `passed` in the first later run of `F` that reported on `M`. Runs that did not report on `M` (a `diff`, `resolve` or `conflict` stage, `--no-verify`, or a filter) are skipped. Its kind comes from comparing the hashes of the two runs:

| `.ts` changed | `.dfy` changed | Kind |
|---|---|---|
| yes | either | `source-fix`: the program or its spec changed. It is labeled at report time. |
| no | yes | `proof`: proof work only. This is not counted as a bug. |
| no | no | `flaky`: the same inputs gave a different result, usually a timeout. |

**A claimcheck catch** is a function that is `disputed` in some run and `confirmed` in the first later run:

| contract changed | spec changed | Kind |
|---|---|---|
| yes | no | `contract-fixed`: the prose claimed something the spec did not say. |
| no | yes | `spec-fixed`: the spec was weaker than the claim. |
| yes | yes | `both-fixed` |
| no | no | `flaky`: claimcheck's LLM step changed its verdict on unchanged input. |

A failure that has no later pass yet is **open**. If a member is missing from a later run that is not `partial`, because it was renamed or deleted, the failure is reported as **dropped**, never as a catch.

Each catch has an ID, formed from the failing run and the member name, such as `r_7f3a:applyDiscount_ensures`.

**Evidence for labeling.** In `--json` output, each `source-fix` catch carries the unified diff of the `.ts` between the two runs' snapshots, the failing run's `errors`, and a mechanical `change` hint:

| `change` | Meaning | Likely label |
|---|---|---|
| `annotations-only` | Every changed line is a `//@` line. | `spec-bug` |
| `code-only` | No changed line is a `//@` line. | `impl-bug` |
| `mixed` | Both kinds of line changed. | Needs judgment. |

The hint is a starting point, not a label. A `code-only` diff can still be an unrelated edit in the same file.

## 5. Labels at report time

Only `source-fix` catches need judgment, because a hash cannot tell a fixed bug from a tightened spec. That judgment is made when a report is requested, not while the work happens.

A reporting skill, `lemmascript-catch-report`, does it. It is meant to run in a clean agent with no stake in the work, in the same way `lemmascript-proof-review` does. The skill:

1. Runs `lsc runs --json` to get every catch not yet covered by a report.
2. For each unlabeled `source-fix` catch, reads the diff, the error that preceded it, and the `change` hint, and records a label:

   ```sh
   npx lsc runs label r_7f3a:applyDiscount_ensures impl-bug "discount could exceed subtotal"
   ```

3. Runs `lsc runs report` to write the dated report, then relays its counts and the `impl-bug` and `spec-bug` catches with their notes.

The labels for a `source-fix` catch are `impl-bug` (the TypeScript computed the wrong thing), `spec-bug` (the `requires` or `ensures` was wrong), and `not-a-bug` (the `.ts` changed for another reason, such as an unrelated edit in the same file). When one change fixed both code and spec, the label is `impl-bug`. `lsc runs label` refuses an ID that is not in the log and a label that does not fit the catch. The label is appended as its own record, and a later label for the same catch replaces an earlier one:

```json
{"type":"label","catch":"r_7f3a:applyDiscount_ensures","label":"impl-bug","note":"discount could exceed subtotal","ts":"..."}
```

Open claimcheck disputes are not labeled by the agent. A dispute is an intent question for the user, so the report lists open disputes with claimcheck's discrepancy text. If the user decides one is a false positive, it is recorded with the label `false-positive` and the user's reason.

## 6. Dated reports

`lsc runs report` writes `.lemmascript/reports/<date>.md`, for example `reports/2026-09-30T2247.md`, and appends a marker to the log:

```json
{"type":"report","id":"rep_2026-09-30T2247","ts":"2026-09-30T22:47:10Z","through":"r_9c2e","file":"reports/2026-09-30T2247.md"}
```

`through` is the last run the report covers. The next report covers the runs after it, so each run is reported exactly once. A run appended while a report is being written falls into the next report.

A report's window decides what it counts:

- **A catch** is counted in the report whose window contains its **passing** run. A failure from before the last report that is fixed now is counted now, and the report shows the date of the original failure.
- **Open failures** are listed in every report while they stay open, with the date each one first failed. They are a current state, not a count, so listing them again is not double counting.
- **Dropped failures** are counted in the report whose window contains the run where the member disappeared.

A report is a snapshot. Labels added or changed later do not rewrite it, and they show up in the next report only if that report covers the catch. To relabel an already-reported catch, record the label and run `lsc runs --all`.

`lsc runs` with no argument prints the same layout for the runs not yet reported, without writing a file or a marker. The mechanical counts come first and the labeled counts after them, so a reader can see which numbers depend on judgment:

```
report 2026-09-30 22:47  (runs 2026-09-28 14:02 → 2026-09-30 22:41, 31 runs, 3 files)
previous report 2026-09-28 13:55

verify:      14 fixed, 2 open (1 since 2026-09-26), 1 dropped
  source-fix   5   (impl-bug 2, spec-bug 2, not-a-bug 0, unlabeled 1)
  proof        8
  flaky        1
  diff-check   3 additions-only violations

claimcheck:  5 resolved, 1 open (1 marked false-positive)
  spec-fixed      2
  contract-fixed  2
  both-fixed      0
  flaky           1

impl-bug   r_7f3a:applyDiscount_ensures   src/domain.ts   failed 2026-09-29
           discount could exceed subtotal
...
```

The report file ends with one line per catch: its kind, label, file, failure date, and note. The illustration above is a mock-up of the intended layout. Real numbers only come from a real log.

## 7. Limits

- **Only runs through `lsc` are recorded.** A bare `dafny verify --filter-symbol=...` is invisible to the log. The `lemmascript` skill already tells agents to finish with `lsc check`, so the passing run is recorded even when they iterate on a single lemma with bare Dafny.
- **Single-lemma iteration is compressed.** Ten attempts with bare Dafny followed by one `lsc check` show up as a single failure and a single pass. The log counts catches, not attempts.
- **The `.ts` hash covers the whole file.** If an unrelated function changed between the failing and passing runs, a proof-only fix is reported as `source-fix`. The diff shows this, and the labeler marks it `not-a-bug`. Hashing each function's extracted IR would remove the case, and could be added later.
- **The labeler sees evidence, not intent.** It has the diff and the error, but not the working agent's reasoning. For telling a code bug from a spec bug this is usually enough; the note records what the labeler concluded.
- **Claimcheck verdicts are not deterministic.** That is why `flaky` is a separate row and is never counted as a fix.
- **Reports live in the ignored log directory.** Deleting `.lemmascript/` deletes them too. A project that wants to keep reports copies them out or commits them deliberately.
- **Snapshots are never pruned automatically.** They are small text files, and identical versions are stored once. Deleting `.lemmascript/` resets the log.
- **The Lean backend is out of scope.** `lsc check --backend=lean` is not recorded in this version.

## 8. Implementation

| File | Change |
|---|---|
| `tools/src/config.ts` | Add a `run-log` registry entry (boolean, default `true`, config-only). |
| `tools/src/run-log.ts` (new) | Create `.lemmascript/` with its `.gitignore`, append records, hash and snapshot files, read Dafny's text results file, derive catches, compute diffs and `change` hints, write labels, write dated reports and their markers. |
| `tools/src/dafny-commands.ts` | `dafnyCheckDiff`, `dafnyVerify` and `dafnyRegen` take an optional log context, and each records the stage it detects; recording lives there only because these helpers end runs with `process.exit`, and would move to `lsc.ts` if they returned outcomes instead. `dafnyVerify` adds `--log-format text` and reads the member outcomes after Dafny exits; Dafny's output stays inherited. |
| `tools/src/lsc.ts` | Pass the log context from resolved options. Record claimcheck results in both branches. Add the `runs`, `runs label`, and `runs report` subcommands. |
| `tools/fixtures/` | One fixture that goes fail → proof fix → pass, one that goes fail → code fix → pass (`code-only`), and one that goes fail → annotation fix → pass (`annotations-only`), checking the derived kinds and hints. |
| `lemmascript-catch-report` skill (new, in lemmascript-skills) | Label unlabeled `source-fix` catches from `lsc runs --json` evidence, list open claimcheck disputes for the user, and write the report. |

The `lemmascript` skill needs no change for logging. The counting logic lives in `lsc`, where it has tests, and the skill only applies judgment on top of it.

## Open questions

1. Should `lsc runs` also read benchmark harness logs, so that benchmark write-ups can quote catch counts directly?
2. Is per-function IR hashing (§7, third limit) worth doing in the first version? It would also make the diff shown to the labeler smaller.
3. Should the `.dfy` be snapshotted too, so a report can show what proof work each `proof` catch took?
4. Should reports be written somewhere tracked by git by default, so they are kept and shared, instead of inside `.lemmascript/`?
