module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Adjoin.PowerBasis

@[expose] public section

/-!
# PRed to Mathlib: `PowerBasis.ofAdjoinSimpleEqTop`

The declarations in this file were extracted from `SKW.Prereqs.KummerExtension` and submitted
upstream as Mathlib PR [#40328](https://github.com/leanprover-community/mathlib4/pull/40328).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.KummerExtension`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

open IntermediateField

/-- Version of `PowerBasis.ofAdjoinEqTop` for `IntermediateField.adjoin`. -/
noncomputable def PowerBasis.ofAdjoinSimpleEqTop {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] {α : L} (h : IsIntegral K α) (hgen : K⟮α⟯ = ⊤) : PowerBasis K L :=
  PowerBasis.ofAdjoinEqTop h (by
    have h := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h.isAlgebraic
    rw [hgen, IntermediateField.top_toSubalgebra] at h
    exact h.symm)

@[simp]
lemma PowerBasis.ofAdjoinSimpleEqTop_gen {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] {α : L} (h : IsIntegral K α) (hgen : K⟮α⟯ = ⊤) :
    (PowerBasis.ofAdjoinSimpleEqTop h hgen).gen = α := by
  simp [PowerBasis.ofAdjoinSimpleEqTop, PowerBasis.ofAdjoinEqTop_gen]

@[simp]
lemma PowerBasis.ofAdjoinSimpleEqTop_dim {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] {α : L} (h : IsIntegral K α) (hgen : K⟮α⟯ = ⊤) :
    (PowerBasis.ofAdjoinSimpleEqTop h hgen).dim = (minpoly K α).natDegree := by
  simp [PowerBasis.ofAdjoinSimpleEqTop, PowerBasis.ofAdjoinEqTop_dim]

end
