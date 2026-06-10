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

@[expose] public section

/-!
# PRed to Mathlib: `Algebra.isSeparable_of_separable_splitting_field`

The declarations in this file were extracted from `SKW.Prereqs.KummerExtension` and submitted
upstream as Mathlib PR [#40339](https://github.com/leanprover-community/mathlib4/pull/40339).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.KummerExtension`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

open Polynomial in
/-- If `p` is a separable polynomial with a splitting field `E` over `F`,
then `E / F` is a separable extension. -/
theorem Algebra.isSeparable_of_separable_splitting_field {F E : Type*} [Field F] [Field E]
    [Algebra F E] {p : F[X]} [sp : Polynomial.IsSplittingField F E p] (hp : p.Separable) :
    Algebra.IsSeparable F E := by
  suffices Algebra.IsSeparable F (⊤ : IntermediateField F E) from
    IsSeparable.of_equiv_equiv (B₁ := (⊤ : IntermediateField F E))
      (RingEquiv.refl F) IntermediateField.topEquiv.toRingEquiv (by ext; simp)
  rw [← (isSplittingField_iff_intermediateField.mp sp).2]
  refine (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).mpr fun x hx ↦ ?_
  exact Polynomial.Separable.of_dvd hp <| minpoly.dvd _ _ <| aeval_eq_zero_of_mem_rootSet hx

open Polynomial in
theorem IsGalois.of_separable_splitting_field' {F E : Type*} [Field F] [Field E]
    [Algebra F E] {p : F[X]} [p.IsSplittingField F E] (hp : p.Separable) :
    IsGalois F E :=
  { to_isSeparable := Algebra.isSeparable_of_separable_splitting_field hp,
    to_normal := Normal.of_isSplittingField p }

end
