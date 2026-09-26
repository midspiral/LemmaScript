# F* proof companions

Each pair corresponds to the TypeScript source one directory up: `binarySearch.fst` and `binarySearch.fst.gen` belong to `../binarySearch.ts`.

- `.fst.gen` is the generated baseline. Do not edit it.
- `.fst` contains the generated program plus any handwritten proofs. Add proofs here, preserving every generated line.

Both files are tracked so regeneration can merge source changes without losing proofs. Pairs are identical when automatic verification needs no proof additions.

From the repository root, run:

```sh
node tools/dist/lsc.js check --backend=fstar examples/binarySearch.ts
./regen-fstar.sh  # regenerate and verify all examples, preserving proofs
```

Use `lsc regen --backend=fstar` after changing a TypeScript source. Verify through `lsc`: it copies the working proof to a temporary filename matching its internal F* module declaration.
