---
title: "Step 2: Define Your Requirements"
description: "Describe your app's state, actions, and rules before writing any code."
---

## What this step is for

Before writing any code, you need to define what your app does and what "correct" means. This is a plain-English document that captures four things:

1. **State**: what data does your app hold?
2. **Actions**: what can users do?
3. **Never**: what can never happen?
4. **Always**: what must always be true?

These map directly to the verification properties you'll write later, but for now, you're just thinking about your app.

## Create REQUIREMENTS.md

Copy the requirements template from LemmaScript into your project root:

```bash
cp ../LemmaScript/templates/REQUIREMENTS.md .
```

This gives you a structured file with four sections and inline guidance for your agent.

## Fill it in

Tell your agent what you're building. For example:

> I want to build a group scheduling poll app called Quorum. People create polls
> with time slots, participants vote on which times work for them, and the app
> picks the best meeting time. For this step, fill out REQUIREMENTS.md.

The agent will draft something like:

```markdown
# Quorum

A group scheduling poll where participants mark their available times
and the app finds the best meeting slot.

## State

### Poll
- title: text
- slots: list of TimeSlot
- members: list of Member
- status: open | closed
- result: list of TimeSlot (the winning slots)

### TimeSlot
- datetime: timestamp

### Member
- name: text

### Vote
- value: yes | no | maybe

Relationships:
- one Vote per (Member, TimeSlot) pair
- a Poll has many TimeSlots
- a Poll has many Members

## Actions

- Create poll: creates a new poll with a title and a set of time slots. Status starts as open.
- Add member: adds a member to a poll.
- Cast vote: a member sets their vote value for a time slot. If a vote already exists, it is replaced.
- Close poll: sets status to closed, computes result.

## Never

- A member votes on a slot that does not belong to the poll
- A member has more than one vote per slot
- A vote is cast on a closed poll
- A non-member votes
- Vote counts go negative

## Always

- The result slot(s) have an availability count >= every other slot
- Vote count for a slot equals the number of yes votes for that slot
- Total votes per member never exceeds total slots in the poll
- A closed poll's result only contains slots that belong to it
```

## Review and iterate

Read through the draft. Ask yourself:

- Is anything missing? ("What about ties?")
- Is anything wrong? ("Actually, 'maybe' shouldn't count toward the winner")
- Is anything vague? ("What does 'best availability' mean exactly?")

Edit directly or tell your agent what to change. This document is your north star for the rest of the build: every verification property you write later traces back to a line here.

## Next step

With requirements defined, you'll write your first LemmaScript-annotated TypeScript: translating these plain-English rules into a domain model with verification properties.
