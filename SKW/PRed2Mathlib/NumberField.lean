module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

/-!
# PRed to Mathlib: totally real versus totally complex

The declarations in this file were extracted from `SKW.Prereqs.NumberField` and submitted
upstream as Mathlib PR [#44527](https://github.com/leanprover-community/mathlib4/pull/44527),
where they are stated with the weaker hypothesis `[Nonempty (InfinitePlace K)]`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.NumberField`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

section TotallyRealComplex

open NumberField

variable (K : Type*) [Field K] [NumberField K]

theorem IsTotallyComplex.not_isTotallyReal [IsTotallyComplex K] : ¬ IsTotallyReal K := by
  intro _
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact IsTotallyComplex.complexEmbedding_not_isReal φ <| IsTotallyReal.complexEmbedding_isReal φ

theorem IsTotallyReal.not_isTotallyComplex [IsTotallyReal K] : ¬ IsTotallyComplex K := by
  intro _
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact IsTotallyComplex.complexEmbedding_not_isReal φ <| IsTotallyReal.complexEmbedding_isReal φ

end TotallyRealComplex
