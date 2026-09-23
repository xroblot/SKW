module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

/-!
# PRed to Mathlib: multiplicity of ideals at the top ideal

The declarations in this file were extracted from `SKW.Prereqs.Ideals` and submitted upstream as
Mathlib PR [#44134](https://github.com/leanprover-community/mathlib4/pull/44134), where they are
named `Ideal.multiplicity_top_right`, `Ideal.emultiplicity_of_top_right` and
`Ideal.finiteMultiplicity`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
(and its import in `SKW.Prereqs.Ideals`) should be deleted, and any usages redirected to the
Mathlib versions.
-/

theorem Ideal.multiplicity_top {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ≠ ⊤) :
    multiplicity I ⊤ = 0 := by
  rw [← one_eq_top, multiplicity_one_right]

theorem Ideal.emultiplicity_top {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ≠ ⊤) :
    emultiplicity I ⊤ = 0 := by
  rw [← one_eq_top, emultiplicity_of_one_right (by rwa [Ideal.isUnit_iff])]

theorem Ideal.IsDedekindDomain.finiteMulticity {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J : Ideal R} (hI : I ≠ ⊤) (hJ : J ≠ ⊥) :
    FiniteMultiplicity I J :=
  FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff]) hJ

end
