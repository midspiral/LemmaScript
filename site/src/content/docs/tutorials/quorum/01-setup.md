---
title: "Step 1: Environment Setup"
description: "Install Node.js, Dafny, and LemmaScript. Verify the toolchain works."
---

## Requirements

- **Node.js 18+**
- **Dafny 4.x+**
- **Git**

## Install Dafny

**macOS:**
```bash
brew install dafny
```

**Linux / Windows:**
Download from [github.com/dafny-lang/dafny/releases](https://github.com/dafny-lang/dafny/releases), extract, and add to your PATH.

Confirm:
```bash
dafny --version
```

## Install LemmaScript

One global install puts the `lsc` toolchain (and companions like `lsc claimcheck`)
on your PATH:

```bash
npm install -g lemmascript
```

## Set up your workspace

Create the project, then clone the agent skills into it — they teach your agent the
annotation grammar and the verification loop, and they carry the Quorum design
document you'll use in the next step:

```bash
mkdir quorum && cd quorum
npm init -y
npm install typescript --save-dev
git clone https://github.com/midspiral/lemmascript-skills <your/skills/dir>
```

`<your/skills/dir>` is wherever your agent discovers skills — for Claude Code
that's `.claude/skills`; other agents have their own location. The tutorial uses
the placeholder throughout; substitute your path.

Your file structure:
```
quorum/
├── <your/skills/dir>/ ← the skills for AI (cloned)
├── package.json
└── (src/ comes later)
```

## Verify the toolchain

```bash
cat > hello.ts << 'EOF'
export function add(a: number, b: number): number {
  //@ verify
  //@ ensures \result === a + b
  return a + b;
}
EOF
```

```bash
lsc gen --backend=dafny hello.ts
dafny verify hello.dfy
```

Expected:
```
Dafny program verifier finished with 1 verified, 0 errors
```

Clean up:
```bash
rm hello.ts hello.dfy hello.dfy.gen
```

## What you've done

- Installed Dafny (the theorem prover) and the LemmaScript toolchain from npm
- Created the project with the agent skills mounted at your agent's skills directory
- Verified the full pipeline works: annotated TypeScript → generated Dafny → proof passes

## Next step

You'll read through the Quorum design document: the spec that drives everything the agent builds from here.
