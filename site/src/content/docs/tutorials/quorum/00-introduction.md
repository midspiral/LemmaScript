---
title: "Introduction"
description: "What we're building, why verification matters, and how this tutorial works."
---

# Build a Verified Core for a Scheduling App

In this tutorial, you'll build **Quorum**: a group scheduling poll (think When2Meet or Doodle) where participants mark their available times and the app picks the best meeting slot.

## What makes this different from a typical React tutorial
The core logic of your app will be **formally verified**. That means you'll have mathematical proof that your app does what it claims. Not just tests that check a few cases, but a guarantee that covers *every* possible input.

The mental model you should go into this tutorial with is this: your app has a small, proven-correct **core**. Everything else is normal software with normal bugs. The value is that an entire class of bugs — often some of the *most critical* — are eliminated entirely.

## What is formal verification?

You already use one form of verification every day: **types**. When TypeScript tells you a function returns `string`, you trust it. You don't write a test asserting the return value isn't a number. The compiler proved it for you.

Formal verification extends that idea to *behavior*. Instead of just "this function returns a number," you can prove "this function returns the index of the slot with the highest vote count" or "this function never allows a member to vote twice."

## Why bother?

For a scheduling poll, the stakes are low. But the technique scales to domains where failure is more expensive:

- Financial calculations that must balance
- Access control that must never leak
- State machines that must never reach invalid states

This tutorial uses a low-stakes app so you can focus on learning the process without worrying about the domain complexity.

## What you'll use

- **LemmaScript**: a toolchain that takes your TypeScript code, reads special comments you've added, and generates a formal model that a theorem prover can check. Your TypeScript runs unchanged; the verification is a parallel process.
- **Dafny**: the theorem prover that checks your proofs. You won't write Dafny directly (LemmaScript generates it), but you'll see its output when verification succeeds or fails.
- **An AI agent** (like Claude Code or Codex): your partner for this build. You'll describe what you want; the agent will draft code and specifications. You review, modify, and direct.

## AI use

LemmaScript was created for use with AI. Of course, you can manually write annotations, review the model against the TypeScript... you could even write your own proofs! But the idea is that you don't have to. Throughout the tutorial, you will be provided with prompts and skills that help guide your agent through each step. We do recommend careful review of the output at first to gain a thorough understanding of how the system works.    

## What we'll build

By the end of this tutorial, Quorum will:

- Let a user create a poll with a set of proposed time slots
- Let participants join and mark which times work for them
- Compute the best meeting time based on everyone's availability
- **Prove** that the computed winner genuinely has the highest availability
- **Prove** that no one can vote twice on the same slot
- **Prove** that vote counts are always consistent with actual votes cast

The app will have a React frontend, verified domain logic, and will be login-free.

## Where bugs can still live

"Verified" does not mean "bug-free everywhere." Here's what the boundary looks like:

**Bugs are extinct in:**
- The domain logic: state transitions, vote counting, winner computation
- The rules: if we say "no double voting," a bug cannot exist that will allow double voting

**Bugs can still live in:**
- The UI: a button wired to the wrong action, a label showing the wrong field
- The network layer: a dropped request, a timeout, a stale cache
- The glue: serializing data to/from the database, parsing user input
- Anything outside `domain.ts`: the verified core is an island of certainty in a sea of unverified code


## Next step

Before writing any code, you'll set up your environment: Node.js, Dafny, and LemmaScript. Then you'll define what "correct" means for Quorum in plain English, before the agent translates it into something provable.
