---
title: "Step 5: Check Your Guarantees"
description: "Audit the proofs against the design document to know exactly what you can claim."
---

## Why this step exists

Proofs passing doesn't mean you've proven everything the design promised. Dafny said "0 errors" — but which properties were actually checked? Are there gaps between what DESIGN.md claims and what the annotations prove? Are any ensures weaker than the spec sketches? Maybe you caught some of these upon initial review, but this is an added sanity check as an independent audit. 

**Note: this is a case where we are using LLM-as-judge. This technique can be quite effective, but it does rely on trust in the LLM. We are working toward improving the toolchain with better audits along the way — fully deterministic audits as well as some hybrid approaches.**



## Open a fresh agent

This works best in a **new agent with no context** from the build process. A clean agent reads the files from scratch and isn't biased by the iteration it just went through. We recommend using this `proof-review` skill to guide the agent. 

If you use the skill, simply call it from the agent; no further instructions needed. 

If not using the skill, tell it:

> Read DESIGN.md, src/domain.ts, src/domain.dfy.gen, and src/domain.dfy.
> Run dafny verify on domain.dfy. Then check the proofs against the design
> document: do the proofs capture the requirements? What guarantees can we
> safely make? Do not change code — create PROOF_FINDINGS.md with your findings.

## What the agent produces

`PROOF_FINDINGS.md` in the project root. [Sample.](https://github.com/midspiral/quorum-tutorial-lemmascript/blob/main/PROOF_FINDINGS.md) It contains:

### Executive summary
What is proven, what is not, overall assessment.

### What is safely guaranteed
One section per property family. For each: what the proof establishes, which contracts support it, and any caveats.

### Design claims: status table
Each claim from DESIGN.md mapped to **supported**, **partially supported**, or **not yet supported**.

For example:

| Design claim | Status |
|---|---|
| Heatmap is exactly the count of free participants per slot | Supported |
| Best recommendation is exactly the positive argmax | Supported |
| Marking more slots never lowers counts | Not yet proved |
| Participant ids are unique | Not proved (trusted shell) |
| Queries over export equal live queries | Not yet proved |

### Main gaps
Numbered list of what's missing before the full product promise can be made.

### Safe external wording
A precise claim that matches exactly what the proofs establish, and a list of what should not be claimed yet.

## What to do with the findings

Read through the gaps. For each one, decide:

- **Fundamental to the core**: this gap undermines a guarantee you care about. It needs to be fixed before moving on.
- **Deferrable**: this is real but can be a later proof stage. Add it to the roadmap.
- **Accepted boundary**: this is outside the verified core by design (shell, infra, trust boundary).

For any gap you classify as fundamental: take `PROOF_FINDINGS.md` back to your **original build agent** and tell it:

> Read PROOF_FINDINGS.md. Strengthen the proofs to close these gaps:
> [list the specific findings]. Then re-run lsc check until verification passes.

After the agent finishes, **re-run the audit**: open another fresh agent and repeat the proof review. Keep iterating until the findings match the guarantees you need.

Update DESIGN.md's roadmap table to reflect the actual state after each round.

## What you've done

- Run an independent audit of proofs against the design document
- Know exactly which claims are supported by proofs and which are not
- Have a precise statement of what the verified core guarantees
- Identified gaps to address now or defer to later stages

## Next step

With a verified and audited domain core, you'll build a thin React UI that imports it directly: dispatching Ops and rendering verified outputs.
