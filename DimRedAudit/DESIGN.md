# Design of the comparator surface

Each group of headline theorems has a directory here with the same four files, and a bridge of
its own under `Support/`.

- `Challenge.lean` imports `Mathlib` and nothing else. It rebuilds from Mathlib primitives
  every object the theorems mention: the sites of `ℤ^d`, the hypercube and its inner
  boundary, the sorted fundamental domain, the Laplacian with dissipating boundary
  conditions, the parallel toppling odometer and sandpile, their terminal values, the topple
  time, the facet point and the simplex maximum. It states the theorems and ends each in a
  single `sorry`. This file is the object of trust: a reader checks what it says, not how it
  is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`). It imports only
  `Mathlib`, so the vocabulary elaborates in the solution exactly as in the challenge.
- `Solution.lean` imports the library together with its own `SolutionBasic` and its own
  bridge in `Support/`, restates the challenge theorems byte-for-byte, and proves them from
  the library's verified statements in `DimRed/MainTheorems.lean`.
- `comparator.json` names the challenge module, the solution module, the theorems and the
  permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and enables the nanoda
  kernel.

The files under `Support/` are part of the solutions: `DimensionalReductionBridge.lean`,
`SelfSimilarityBridge.lean`, `SandpileBridge.lean` and `RegularityBridge.lean`, one for each
pair, each importing the `SolutionBasic` of its pair and nothing of the other pairs. A bridge
identifies the challenge's definitions with the library's. The vocabulary declares no new
type, so the non-recursive definitions agree with the library's by `rfl` or by unfolding; the
odometer is defined by recursion on time, so `odo_eq` is an induction on time and the
equalities for the objects built on it follow by rewriting. A bridge keeps only the lemmas its
solution uses, with those they depend on. The same lemma has the same statement in every
bridge that contains it.

The vocabulary is the same block in all four challenges, so the four `SolutionBasic` files
are the same text; they are separate files so that each pair imports its own copy and no
pair depends on another. For the same reason no module imports several solutions at once:
the comparator itself checks each solution statement against its challenge, constant by
constant through the whole dependency closure, and the closure against Mathlib.

The public workflow feeds each pair to
[leanprover/comparator](https://github.com/leanprover/comparator), which elaborates both
statements and requires them to coincide, replays the solution's proof through an independent
implementation of the Lean kernel, and rejects any axiom outside the permitted three. Nothing
a solution imports can change the statement the reader saw in the challenge; it can only
supply a kernel-checked proof of it.

`check_standalone.sh` elaborates a challenge on its own, with the library's build options, to
confirm that it depends on Mathlib alone, and with `--vocabulary` checks that the vocabulary
block is byte-identical in each `Challenge.lean` and the `SolutionBasic.lean` beside it.
