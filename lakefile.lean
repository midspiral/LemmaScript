import Lake
open Lake DSL System

require velvet from ".." / "velvet"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

package LemmaScript where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

lean_lib LemmaScript

@[default_target]
lean_lib Examples where
  srcDir := "examples"
  roots := #[
    `«binarySearch.types», `«binarySearch.spec», `«binarySearch.def», `«binarySearch.proof»,
    `«arraySum.spec», `«arraySum.def», `«arraySum.proof»,
    `«linearSearch.def», `«linearSearch.proof»,
    `«transition.types», `«transition.spec», `«transition.def», `«transition.proof»,
    `«packet.types», `«packet.def», `«packet.proof»,
    `«maxElement.def», `«maxElement.proof»,
    `«isSorted.def», `«isSorted.proof»,
    `«arrayContains.def», `«arrayContains.proof»,
    `«hof.types», `«hof.def», `«hof.proof»,
    `«spec.types», `«spec.def», `«spec.proof»,
    `«clamp.def», `«clamp.proof»,
    `«clampAll.def», `«clampAll.proof»,
    `«toposort.spec», `«toposort.def», `«toposort.proof»,
    `«majority.types», `«majority.spec», `«majority.def», `«majority.proof»,
    `«perm.types», `«perm.def», `«perm.proof»,
    `«unionInArray.types», `«unionInArray.def»,
    `«truthiness.types», `«truthiness.def», `«truthiness.proof»,
    `«iff.types», `«iff.def», `«iff.proof»,
    `«setFromArray.types», `«setFromArray.def», `«setFromArray.proof»,
    `«templateConcat.types», `«templateConcat.def», `«templateConcat.proof»,
    `«nestedPush.types», `«nestedPush.def», `«nestedPush.proof»,
    `«discriminantTrailing.types», `«discriminantTrailing.def», `«discriminantTrailing.proof»,
    `«spreadMerge.types», `«spreadMerge.def»,
    `«recordIndexByEnum.types», `«recordIndexByEnum.def»,
    `«leftPad.def», `«leftPad.proof»,
    `«swap.def»,
    `«andChainStmt.types», `«andChainStmt.def»,
    `«postTags.types», `«postTags.def»,
    `«nameClash.types», `«nameClash.def»,
    `«tuples.types», `«tuples.def», `«tuples.proof»,
    `«forContinue.types», `«forContinue.def», `«forContinue.proof»,
    `«arrayFind.types», `«arrayFind.def»,
    `«ctorName.types», `«ctorName.def»,
    `«switchEnumField.types», `«switchEnumField.def», `«switchEnumField.proof»
  ]
