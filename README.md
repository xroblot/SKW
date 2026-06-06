# SKW

A formalization in Lean 4 / Mathlib of the Stickelberger theorem and the Kronecker-Weber
theorem. **This is a work in progress.**

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

Some intermediate results still contain `sorry`s. The
[blueprint](https://xroblot.github.io/SKW/blueprint/) tracks the mathematical proof and
its Lean status, and the [dependency graph](https://xroblot.github.io/SKW/blueprint/dep_graph_document.html)
shows which pieces are already formalized.

## Acknowledgements

This project relies on [Mathlib](https://github.com/leanprover-community/mathlib4), the
Lean community's mathematical library, and on the
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) and
[`doc-gen4`](https://github.com/leanprover/doc-gen4) tools for the blueprint and
documentation websites.
