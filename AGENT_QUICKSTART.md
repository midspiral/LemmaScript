# LemmaScript quick start for agents

Set up LemmaScript in this repo and verify one function with it.

1. Check for Node >= 18 and Dafny 4.x. Install Dafny if it is missing (https://dafny.org/latest/Installation).
2. Run: `npm install -g lemmascript`
3. Clone https://github.com/midspiral/lemmascript-skills into your skills directory and read the main `lemmascript` skill before doing anything else.
4. Pick one small, pure TypeScript function in this repo with real logic (arithmetic, bounds, parsing, state transitions). Tell the user which one and why. If there is no suitable function, write a small one (e.g. a clamp or a binary search) and verify that.
5. Add `//@ contract`, `//@ requires` and `//@ ensures` annotations to it. Do not change the code itself.
6. Run: `lsc check --backend=dafny path/to/file.ts`
7. If it fails, read the error and fix the contract or add proof to the `.dfy` file. Never edit the `.dfy.gen` file and never use `//@ assume` to make it pass.
8. Report what is now proven, in plain English, and anything the verifier caught.
