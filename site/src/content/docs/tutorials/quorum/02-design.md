---
title: "Step 2: The Design Document"
description: "Understand the DESIGN.md that drives the verified core."
---

## Why a design document?

Before writing any code, a LemmaScript project should have a DESIGN.md. This document captures:

- What the app does
- What is verified and what is not
- The data model the verified core operates on
- The properties you'll prove, spelled out as LemmaScript spec sketches
- The architecture: where the verified core sits, what surrounds it

The DESIGN.md is how you tell it exactly what "correct" means.  

## What's in a DESIGN.md

The document has a consistent structure:

1. **The product**: what does the app do? One paragraph.
2. **The promise**: what IS verified, and what is NOT. This is the trust boundary. Be precise about both sides.
3. **The key design insight**: the structural property of your domain that makes verification tractable. For Quorum, it's that availability is partitioned by participant: nobody edits anyone else's row, so there are no conflicts.
4. **Data model**: TypeScript interfaces with `//@ backend dafny`. The verified core uses abstract indices, not database IDs. Containment, not foreign keys.
5. **Architecture**: how the verified core connects to the UI and backend. The core runs everywhere: client, server, query endpoint. Same import, no adapter.
6. **Properties**: grouped into families (well-formedness, aggregation correctness, monotonicity, convergence). Each property gets a LemmaScript spec sketch showing the actual annotation.
7. **Verification approach**: conventions the agent should follow (pure recursive functions, total kernel, staged proofs).
8. **Roadmap**: staged proof table. Each stage is shippable.
9. **Open questions**: what's deferred, what's unresolved.

## The Quorum design document

For this tutorial, we've written the DESIGN.md for you. It describes a when2meet-style scheduling app whose verified core guarantees:

**Note: When building on your own, you can use our design-doc skill, which is in `quorum-tutorial/.claude/skills/design-doc`**

[TODO @fernanda: are these really the only guarantees it makes?]
1. The heatmap counts are exact
2. The best-time recommendation flags the actual argmax slots
3. More availability only helps (monotonicity)
4. Order doesn't matter: edits converge regardless of arrival sequence
5. The export round-trips faithfully

Copy it into your project root:

```bash
cp ../.claude/skills/design-doc/DESIGN_QUORUM.md ./DESIGN.md
```

Read through it. The sections you'll interact with most in the next steps:

- **§5 (Data model)**: this is what becomes your `domain.ts` interfaces
- **§7 (Properties)**: these become your `//@ ensures` annotations
- **§2 (The promise)**: this is how you'll know when you're done

## For your own app

When building your own verified app, use the `design-doc` skill provided to tell your agent:

> I want to build [description of your app]. Write a DESIGN.md following the LemmaScript
> design document format.

The agent will draft the full document. Review it the same way: does the promise match what you care about? Does the data model use containment? Are the properties precise enough to verify? Iterate manually or with your agent. 

## A note on design specs

This design doc is a starting point. While having a good understanding of your app domain is important when making initial decisions about what to verify and the shape of the core, iteration will be inevitible.

## What you've done

- Understood the structure of a LemmaScript design document
- Copied the Quorum DESIGN.md into your project
- Identified the key sections: data model (§5), properties (§7), and the promise (§2)

## Next step

With the design in hand, you'll build the domain core: the agent translates the data model and properties from DESIGN.md into `src/domain.ts`.
