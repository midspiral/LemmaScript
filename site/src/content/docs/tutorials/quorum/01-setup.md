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

## Set up your workspace

LemmaScript needs to be a sibling directory to your project. Create a parent folder that holds both:

```bash
mkdir quorum-tutorial && cd quorum-tutorial
```

Clone LemmaScript inside it:
```bash
git clone https://github.com/midspiral/LemmaScript.git
cd LemmaScript 
npm install && npm run build

```

Create your app directory next to it:
```bash
mkdir quorum && cd quorum
npm init -y
npm install typescript --save-dev
```

Your file structure:
```
quorum-tutorial/
├── LemmaScript/    ← the toolchain (cloned)
└── quorum/         ← your app (you are here)
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
npx tsx ../LemmaScript/tools/src/lsc.ts gen --backend=dafny hello.ts
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

- Installed Dafny (the theorem prover) and LemmaScript (the toolchain)
- Set up a sibling directory layout: `LemmaScript/` next to `quorum/`
- Verified the full pipeline works: annotated TypeScript → generated Dafny → proof passes

## Next step

You'll read through the Quorum design document: the spec that drives everything the agent builds from here.
