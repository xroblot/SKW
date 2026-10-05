# SKW

A formalization in Lean 4 / Mathlib of the Stickelberger theorem and the Kronecker-Weber
theorem. **Both theorems are now formalized**, modulo a handful of statements that are
waiting on Mathlib pull requests (see [Status](#status) below).

## Links

* [Blueprint](https://xroblot.github.io/SKW/blueprint/)
* [Blueprint as pdf](https://xroblot.github.io/SKW/blueprint.pdf)
* [Dependency graph](https://xroblot.github.io/SKW/blueprint/dep_graph_document.html)
* [Documentation pages for this repository](https://xroblot.github.io/SKW/docs/)
* [Lean Zulip channel](https://leanprover.zulipchat.com/) for coordination

## What are these theorems?

**Stickelberger's theorem** describes how prime ideals of `ℤ[ζ]` (where `ζ` is a root of
unity) factor in terms of Gauss sums: it produces an explicit element of the group ring
`ℤ[Gal(ℚ(ζ)/ℚ)]` — the *Stickelberger element* — that annihilates the class group of
`ℚ(ζ)`. In this project it is stated as `Stickelberger` (in
[`SKW/Stickelberger/Stickelberger.lean`](SKW/Stickelberger/Stickelberger.lean)): a certain
product of Galois conjugates of a prime ideal `𝔭` above `p` is principal.

**The Kronecker-Weber theorem** states that every abelian extension of `ℚ` is contained in
a cyclotomic field `ℚ(ζₙ)` for some `n`. It is stated as `kronecker_weber` (in
[`SKW/KroneckerWeber/KroneckerWeber.lean`](SKW/KroneckerWeber/KroneckerWeber.lean)). The
proof formalized here proceeds by reducing to abelian extensions of prime power degree
ramified at a single prime, and derives the Kronecker-Weber theorem from Stickelberger's
theorem following the approach of Lemmermeyer's paper
[*Kronecker-Weber via Stickelberger*](https://arxiv.org/abs/1108.5671).

## Status

Both `Stickelberger` and `kronecker_weber` are proved, and no file of this project contains
a `sorry` of its own. What remains are thirteen statements admitted on purpose, each of
them a result already submitted to Mathlib and awaiting review; until those land,
`#print axioms kronecker_weber` still reports `sorryAx`.

In [`SKW/Prereqs/OtherPR.lean`](SKW/Prereqs/OtherPR.lean):

| PR | content |
|---|---|
| [#36733](https://github.com/leanprover-community/mathlib4/pull/36733) | decomposition field and inertia field of a prime |
| [#43088](https://github.com/leanprover-community/mathlib4/pull/43088) | maximal quadratic orders over `ℤ` |
| [#43490](https://github.com/leanprover-community/mathlib4/pull/43490) | quadratic fields and their discriminant |
| [#43491](https://github.com/leanprover-community/mathlib4/pull/43491) | the discriminant of `ℚ(√d)` |
| [#43493](https://github.com/leanprover-community/mathlib4/pull/43493) | complex embeddings of quadratic fields |

and in [`SKW/Prereqs/Digits.lean`](SKW/Prereqs/Digits.lean), one lemma from
[#40302](https://github.com/leanprover-community/mathlib4/pull/40302) (`digitsAppend` API).

As each PR is merged, the corresponding stub is deleted and its uses redirected to the
upstream name. The [blueprint](https://xroblot.github.io/SKW/blueprint/) tracks the
mathematical proof and its Lean status, and the
[dependency graph](https://xroblot.github.io/SKW/blueprint/dep_graph_document.html) shows
how the pieces fit together.

## Acknowledgements

Parts of this formalization were written with [Claude Code](https://claude.com/claude-code)
as an assistant. Beyond searching Mathlib for existing results, drafting and shortening
proofs, carrying out mechanical refactorings (renamings, moving material to its proper
file, following the Mathlib naming conventions) and keeping the blueprint in step with the
Lean code, Claude also took part in the mathematics: finding the right form for several
statements, proposing the proof of some intermediate steps, and spotting where an argument
could be simplified or made more general.

This project relies on [Mathlib](https://github.com/leanprover-community/mathlib4), the
Lean community's mathematical library, and on the
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) and
[`doc-gen4`](https://github.com/leanprover/doc-gen4) tools for the blueprint and
documentation websites.
