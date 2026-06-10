module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section

/-!
# Complements to Mathlib.FieldTheory.Normal.Basic

This file contains lemmas that complement results in Mathlib's `Normal.Basic` file,
intended for eventual upstreaming.
-/

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

open IntermediateField in
/-- Algebra version of `splits_of_mem_adjoin`: if a set of algebraic elements have minimal
polynomials that split in another extension `L/F`, then so does any element of the subalgebra
they generate. -/
theorem splits_of_mem_algebraAdjoin {L : Type*} [Field L] [Algebra F L] {S : Set K}
    (hS : ∀ x ∈ S, IsIntegral F x ∧ ((minpoly F x).map (algebraMap F L)).Splits) {a : K}
    (hx : a ∈ Algebra.adjoin F S) : ((minpoly F a).map (algebraMap F L)).Splits :=
  splits_of_mem_adjoin _ _ hS (algebra_adjoin_le_adjoin F S hx)

open Algebra in
/-- A field extension is normal if it is generated (as an algebra) by elements with
splitting minimal polynomials. -/
theorem Normal.of_algebra_adjoin_eq_top {S : Set K} (ht : Algebra.adjoin F S = ⊤)
    (hS : ∀ x ∈ S, IsIntegral F x ∧ ((minpoly F x).map (algebraMap F K)).Splits) :
    Normal F K := by
  refine normal_iff.mpr fun x ↦ ⟨?_, splits_of_mem_algebraAdjoin hS <| ht ▸ mem_top⟩
  exact (isIntegral_algEquiv Subalgebra.topEquiv.symm).mp <|
    (ht ▸ IsIntegral.adjoin (fun x hx ↦ (hS x hx).1)).isIntegral ⟨x,  mem_top⟩

open IntermediateField in
theorem IsScalarTower.adjoin_range_toAlgHom' (F K E : Type*) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] (t : Set E) :
    IntermediateField.restrictScalars F (adjoin (↑(toAlgHom F K E).fieldRange) t) =
      IntermediateField.restrictScalars F (adjoin K t) := by
  have : Set.range (algebraMap (toAlgHom F K E).fieldRange E) = Set.range (algebraMap K E) := by
    ext; simp
  exact IntermediateField.ext fun x ↦ by simp [adjoin, this]

open Polynomial in
theorem IsGalois.map_minpoly_dvd_prod_minpoly (F K : Type*) {E : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] [IsGalois F K]
    [FiniteDimensional F K] (α : E) :
    map (algebraMap F K) (minpoly F α) ∣ ∏ σ : Gal(K/F), map σ (minpoly K α) := by
  classical
  obtain ⟨N, hN⟩ : ∏ σ : Gal(K/F), map σ (minpoly K α) ∈ lifts (algebraMap F K) := by
    refine (lifts_iff_coeff_lifts _).mpr fun n ↦ (IsGalois.mem_bot_iff_fixed _).mpr fun τ ↦ ?_
    have {σ : Gal(K/F)} : (τ : K →+* K).comp (τ⁻¹ * σ) = σ.toRingHom := by ext; simp
    nth_rewrite 1 [← Equiv.prod_comp (Equiv.mulLeft τ⁻¹)]
    simp [← AlgEquiv.toAlgHom_apply, ← AlgHom.coe_toRingHom, ← coeff_map, Polynomial.map_prod,
      map_map, AlgEquiv.toAlgHom_toRingHom, this]
  suffices minpoly F α ∣ N from hN ▸ map_dvd (algebraMap F K) this
  refine minpoly.dvd_iff.mpr ?_
  rw [coe_mapRingHom] at hN
  rw [← eval_map_algebraMap, IsScalarTower.algebraMap_eq F K E, ← map_map, hN,
    Polynomial.map_prod, eval_prod, ← Finset.univ.mul_prod_erase _ (Finset.mem_univ AlgEquiv.refl)]
  simp

-- open IntermediateField in
-- /-- If `K` is generated over `F` by `S`, then the field generated over `K` by `T` (viewed
-- as an `F`-extension) equals the field generated over `F` by `S ∪ T`.
-- Intermediate field analog of `Algebra.adjoin_eq_adjoin_union`. -/
-- theorem IntermediateField.adjoin_eq_adjoin_union' {F E : Type*} [Field F] [Field E] [Algebra F E]
--     {K : IntermediateField F E} {S : Set E} (hK : adjoin F S = K) (T : Set E) :
--     restrictScalars F (adjoin K T) = adjoin F (S ∪ T) := by
--   rw [restrictScalars_adjoin_eq_sup, ← hK, ← adjoin_union]

-- open IntermediateField in
-- /-- If `K` is generated over `F` by `S`, then the field generated over `K` by `T` (viewed
-- as an `F`-extension) equals the field generated over `F` by `S ∪ T`.
-- Intermediate field analog of `Algebra.adjoin_eq_adjoin_union`. -/
-- theorem IntermediateField.adjoin_eq_adjoin_union {F E : Type*} [Field F] [Field E]
--     [Algebra F E] {K : IntermediateField F E}
--     {S : Set K} (hS : adjoin F S = ⊤) (T : Set E) :
--     restrictScalars F (adjoin K T) = adjoin F (algebraMap K E '' S ∪ T) := by
--   rw [restrictScalars_adjoin_eq_sup, adjoin_union, ← IsScalarTower.coe_toAlgHom' F K E,
--     ← adjoin_map, hS, ← AlgHom.fieldRange_eq_map]
--   congr
--   ext; simp

open IntermediateField in
/-- If all generators of an intermediate field adjoin are integral over the base, then so is
every element of the adjoin. -/
theorem IntermediateField.adjoin_isIntegral {K L : Type*} [Field K] [Field L]
    [Algebra K L] {S : Set L} (hS : ∀ x ∈ S, IsIntegral K x) :
    Algebra.IsIntegral K (adjoin K S) := by
  have : Algebra.IsIntegral K (adjoin K S).toSubalgebra := by
    rw [adjoin_toSubalgebra_of_isAlgebraic (fun y hy ↦ (hS y hy).isAlgebraic)]
    exact Algebra.IsIntegral.adjoin hS
  exact this

open IntermediateField in
/-- A field extension is normal if it is generated (as an intermediate field) by elements with
splitting minimal polynomials. -/
theorem Normal.of_adjoin_eq_top {S : Set K} (ht : adjoin F S = ⊤)
    (hS : ∀ x ∈ S, IsIntegral F x ∧ ((minpoly F x).map (algebraMap F K)).Splits) :
    Normal F K := by
  refine normal_iff.mpr fun x ↦ ⟨?_, splits_of_mem_adjoin _ _ hS <| ht ▸ mem_top⟩
  refine (isIntegral_algEquiv topEquiv.symm).mp <| ?_
  exact (ht ▸ IntermediateField.adjoin_isIntegral (fun y hy ↦ (hS y hy).1)).isIntegral
    (topEquiv.symm x)

end
