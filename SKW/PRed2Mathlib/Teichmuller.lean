module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.RootsOfUnity.Basic

set_option linter.style.header false

@[expose] public section

/-!
# PRed to Mathlib: `rootsOfUnity.mapQuot`

The declarations in this file were extracted from `SKW.Stickelberger.Teichmuller` and submitted
upstream as Mathlib PR [#44588](https://github.com/leanprover-community/mathlib4/pull/44588),
which generalizes the existing `Ideal.rootsOfUnityMapQuot` from the ring of integers of a number
field to any commutative ring, in the new file `Mathlib/RingTheory/RootsOfUnity/Quotient.lean`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Stickelberger.Teichmuller` should be deleted, and the usages redirected to
`Ideal.rootsOfUnityMapQuot`, whose arguments come in the other order: `rootsOfUnityMapQuot I n`
against `rootsOfUnity.mapQuot n I` here.
-/

variable {R : Type*} [CommRing R] (n : ℕ) (I : Ideal R)

/--
For `I` an ideal of `R`, the group morphism from the roots of unity of `R`
of order `n` to `(R ⧸ I)ˣ`.
-/
def rootsOfUnity.mapQuot : (rootsOfUnity n R) →* (R ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict _

@[simp]
theorem rootsOfUnity.coe_mapQuot (x : rootsOfUnity n R) :
    (rootsOfUnity.mapQuot n I x).val = Ideal.Quotient.mk I x.val := rfl
