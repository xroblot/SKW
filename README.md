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
`ℚ(ζ)`. In this project it is stated as
[`stickelberger_theorem`](https://xroblot.github.io/SKW/docs/SKW/Stickelberger/Stickelberger.html#stickelberger_theorem):
the Stickelberger element annihilates the ideal class group of a cyclotomic field.

**The Kronecker-Weber theorem** states that every abelian extension of `ℚ` is contained in
a cyclotomic field `ℚ(ζₙ)` for some `n`. It is stated as
[`kronecker_weber`](https://xroblot.github.io/SKW/docs/SKW/KroneckerWeber/KroneckerWeber.html#kronecker_weber).
The proof formalized here proceeds by reducing to abelian extensions of prime power degree
ramified at a single prime, and derives the Kronecker-Weber theorem from Stickelberger's
theorem following the approach of Lemmermeyer's paper
[*Kronecker-Weber via Stickelberger*](https://arxiv.org/abs/1108.5671).

## Status

Both `Stickelberger` and `kronecker_weber` are proved, and no file of this project contains
a `sorry` of its own. What remains are ten statements admitted on purpose, each of them a
result submitted to Mathlib and awaiting review; until those land,
`#print axioms kronecker_weber` still reports `sorryAx`.

| PR | content | statements |
|---|---|---|
| [#35808](https://github.com/leanprover-community/mathlib4/pull/35808) | primes of an inertia ring are unramified | 1 |
| [#35991](https://github.com/leanprover-community/mathlib4/pull/35991) | inertia field of a prime in an intermediate extension | 1 |
| [#36733](https://github.com/leanprover-community/mathlib4/pull/36733) | degree over the inertia field is the ramification index | 1 |
| [#36843](https://github.com/leanprover-community/mathlib4/pull/36843) | a compositum of unramified extensions is unramified | 1 |
| [#43490](https://github.com/leanprover-community/mathlib4/pull/43490) | quadratic fields and their discriminant | 3 |
| [#43493](https://github.com/leanprover-community/mathlib4/pull/43493) | complex embeddings of quadratic fields | 1 |
| [#44588](https://github.com/leanprover-community/mathlib4/pull/44588) | reduction of roots of unity modulo an ideal | 1 |
| [#45512](https://github.com/leanprover-community/mathlib4/pull/45512) | reduction modulo `ζ - 1` in a cyclotomic field | 1 |

All but the one from #44588 live in
[`SKW.Prereqs.OtherPR`](https://xroblot.github.io/SKW/docs/SKW/Prereqs/OtherPR.html), which also
states a few other results of these PRs that the proof does not use; the one from #44588 is in
[`SKW.PRed2Mathlib.Teichmuller`](https://xroblot.github.io/SKW/docs/SKW/PRed2Mathlib/Teichmuller.html).

As each PR is merged, the corresponding stub is deleted and its uses redirected to the
upstream name. The [blueprint](https://xroblot.github.io/SKW/blueprint/) tracks the
mathematical proof and its Lean status, and the
[dependency graph](https://xroblot.github.io/SKW/blueprint/dep_graph_document.html) shows
how the pieces fit together.

## Organization

* `SKW/Stickelberger/Teichmuller.lean`, `SKW/Stickelberger/Stickelberger.lean` and
  `SKW/KroneckerWeber/KroneckerWeber.lean` contain the main development.
* `SKW/Prereqs/Stickelberger.lean` and `SKW/Prereqs/KroneckerWeber.lean` gather the general
  results these files need that are not (yet) in Mathlib.
* `SKW/Prereqs/OtherPR.lean` holds the admitted statements listed above, and `SKW/PRed2Mathlib/`
  the results already submitted to Mathlib, to be deleted once merged.
* `SKW/Upstream.lean` collects results not needed for the proof but worth adding to Mathlib.
* `Archive/` keeps older material that is no longer built.

## License

This project is released under the [Apache 2.0 license](LICENSE), the same license as
Mathlib.

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
