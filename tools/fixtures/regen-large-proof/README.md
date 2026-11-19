# Large proof merge fixture

Reduced from `packages/core/test/machine-model/formal/machineModel.dfy` and
`.dfy.gen` in [robertpenner/xstate at e9042e7](https://github.com/robertpenner/xstate/tree/e9042e7/packages/core/test/machine-model/formal),
using the proof-block layout described in [LemmaScript #280](https://github.com/midspiral/LemmaScript/issues/280).
The upstream MIT license is included in `LICENSE`.

`base.txt` has 32 generated lines; `proof.txt` preserves them with 513 inserted
lines. Changing `below(candidate.node.path, kept.node.path)` to
`below(kept.node.path, candidate.node.path)` conflicts with Git's default merge
diff, but merges exactly with `--diff-algorithm=minimal` (Git 2.54.0).
These are line-based merge inputs, not valid Dafny programs. Keep their blank
lines, indentation, and LF line endings: repeated braces and the distance
between matches are what exercise the diff heuristic.
