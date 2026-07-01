module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.GroupTheory.FiniteAbelian.Duality

public import SKW.PRed2Mathlib.IntermediateFields
public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.Torsion

@[expose] public section

/-! ### Intermediate Fields -/

/-- The fixing subgroup of an intermediate field `F` is a Galois group of `L / F`. This bridges
`IntermediateField.fixingSubgroup` to `IsGaloisGroup.intermediateField`, which is stated on the raw
`fixingSubgroup Gal(L/K) (↑F)`; instance search does not unfold the `IntermediateField.fixingSubgroup`
wrapper on its own, so without this the instance is not found for the `IntermediateField` form. -/
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) : IsGaloisGroup F.fixingSubgroup F L :=
  inferInstanceAs (IsGaloisGroup (fixingSubgroup Gal(L/K) (F : Set L)) F L)

open scoped NumberField in
/-- Ring-of-integers form of the previous instance. The generic `IsGaloisGroup G (𝓞 K) (𝓞 L)`
instance does not fire for `G = F.fixingSubgroup` on its own, so we bridge it explicitly (its body,
`IsGaloisGroup.of_isFractionRing`, uses the field instance above). Keying on `F.fixingSubgroup` (as
opposed to an arbitrary `G`) is essential: it pins the intermediate field `F`, which otherwise would
only be recoverable from `𝓞 ↑F` and hence left undetermined by instance search. -/
instance {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (F : IntermediateField K L) :
    IsGaloisGroup F.fixingSubgroup (𝓞 F) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing _ (𝓞 F) (𝓞 L) F L

open Module in
lemma IntermediateField.finrank_sup_eq_of_inf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional F K] [FiniteDimensional F L]
    [Algebra K ↑(K ⊔ L)] [IsScalarTower F K ↑(K ⊔ L)] (hinf : K ⊓ L = ⊥) :
    finrank K ↑(K ⊔ L) = finrank F L := by
  rw [← mul_right_inj', ← (LinearDisjoint.of_inf_eq_bot hinf).finrank_sup, finrank_mul_finrank]
  exact finrank_pos.ne'

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
open Module in
theorem IntermediateField.finrank_sup_mul_finrank_inf_eq {k L : Type*} [Field k] [Field L] [Algebra k L]
    (E F : IntermediateField k L) [FiniteDimensional k E]  [FiniteDimensional k F] [IsGalois k E] :
    finrank k ↑(E ⊔ F) * finrank k ↥(E ⊓ F) = finrank k E * finrank k F := by
  let : Algebra E ↑(E ⊔ F) := (inclusion le_sup_left).toRingHom.toAlgebra
  have : FiniteDimensional k ↑(E ⊓ F) := FiniteDimensional.of_injective
    (IntermediateField.inclusion inf_le_left).toLinearMap
    (RingHom.injective _)
  suffices h : finrank E ↑(E ⊔ F) = finrank ↑(E ⊓ F) F by
    rwa [← finrank_mul_finrank k E ↑(E ⊔ F), ← finrank_mul_finrank k ↑(E ⊓ F) F, mul_assoc,
      mul_right_inj' finrank_pos.ne', mul_comm, mul_right_inj' finrank_pos.ne']
  let : Algebra ↑(E ⊓ F) ↑(E ⊔ F) := (inclusion inf_le_sup).toRingHom.toAlgebra
  have : IsScalarTower ↑(E ⊓ F) E ↑(E ⊔ F) := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional ↑(E ⊓ F) E := FiniteDimensional.right k _ _
  have : FiniteDimensional ↑(E ⊓ F) F := FiniteDimensional.right k _ _
  have : finrank ↑(E ⊓ F) E ≠ 0 := finrank_pos.ne'
  rw [← mul_right_inj' this, finrank_mul_finrank]
  let E' : IntermediateField ↑(E ⊓ F) L := E.extendScalars (F := E ⊓ F) inf_le_left
  let F' : IntermediateField ↑(E ⊓ F) L := F.extendScalars (F := E ⊓ F) inf_le_right
  let : Algebra E' ↑(E' ⊔ F') := (inclusion le_sup_left).toRingHom.toAlgebra
  let e' : E ≃ₐ[↑(E ⊓ F)] E' := AlgEquiv.refl
  let f' : F ≃ₐ[↑(E ⊓ F)] F' := AlgEquiv.refl
  let h : ↑(E' ⊔ F') ≃ₗ[↑(E ⊓ F)] ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup) :=
    LinearEquiv.ofEq ↑(E' ⊔ F').toSubalgebra.toSubmodule
      ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup).toSubalgebra.toSubmodule
        (by simpa using (extendScalars_sup (F := E ⊓ F) inf_le_left inf_le_right))
  have : IsGalois ↑(E ⊓ F) E' := by
    have : IsGalois ↑(E ⊓ F) E := IsGalois.tower_top_of_isGalois k _ _
    exact IsGalois.of_algEquiv e'
  have : FiniteDimensional ↑(E ⊓ F) E' := Module.Finite.equiv e'.toLinearEquiv
  have : FiniteDimensional ↑(E ⊓ F) F' := Module.Finite.equiv f'.toLinearEquiv
  calc finrank ↑(E ⊓ F) ↑(E ⊔ F)
      = finrank ↑(E ⊓ F) ↑(E' ⊔ F') := ?_
    _ = finrank ↑(E ⊓ F) E' * finrank E' ↑(E' ⊔ F') := by rw [finrank_mul_finrank]
    _ = finrank ↑(E ⊓ F) E * finrank E' ↑(E' ⊔ F') := by rw [e'.toLinearEquiv.finrank_eq]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F' := by
        rw [← finrank_sup_eq_of_inf_eq_bot E' F']
        ext; simp [E', F', mem_bot]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F := by rw [f'.toLinearEquiv.finrank_eq]
  · rw [LinearEquiv.finrank_eq (M := ↑(E ⊔ F)) (N := ↑(E' ⊔ F'))]
    exact (LinearEquiv.refl ↑(E ⊓ F) ↑(E ⊔ F)).trans h.symm

open IntermediateField in
/-- Every finite-dimensional abelian Galois extension `K/F` is the compositum of cyclic
subextensions of prime power degree. (The character codomain is `AlgebraicClosure ℚ`, which has
enough roots of unity for the finite group `Gal(K/F)` regardless of the characteristic of `F`.) -/
lemma IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top
    (F : Type*) (K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsAbelianGalois F K] :
    ∃ (ι : Type u) (_ : Fintype ι) (C : ι → IntermediateField F K),
      (∀ i, IsGalois F (C i) ∧ IsCyclic Gal((C i)/F) ∧ IsPrimePow (Module.finrank F (C i))) ∧
        ⨆ i, C i = ⊤ := by
  classical
  let : CommGroup (K ≃ₐ[F] K) := IsMulCommutative.instCommGroup
  refine ⟨{χ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ // IsPrimePow (orderOf χ)}, Fintype.ofFinite _,
    fun χ ↦ IntermediateField.fixedField χ.1.ker, fun ⟨χ, hχ⟩ ↦ ?_, ?_⟩
  · refine ⟨IsGalois.of_fixedField_normal_subgroup χ.ker, ?_, ?_⟩
    · exact isCyclic_of_injective (IsGalois.normalAutEquivQuotient χ.ker).symm.toMonoidHom
        (MulEquiv.injective _)
    · have : IsGalois F (fixedField χ.ker) := IsGalois.of_fixedField_normal_subgroup χ.ker
      rw [← IsGalois.card_aut_eq_finrank]
      erw [Nat.card_congr (IsGalois.normalAutEquivQuotient χ.ker).symm.toEquiv]
      rwa [MonoidHom.card_quotient_ker_eq_orderOf χ]
  · simp only [← IsGalois.intermediateFieldEquivSubgroup.apply_eq_iff_eq, OrderIso.map_iSup,
      IsGalois.intermediateFieldEquivSubgroup_apply, fixingSubgroup_fixedField, OrderIso.map_top,
      ← toDual_iInf, OrderDual.toDual_eq_top]
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
    by_contra! h
    have h_eq_one {ψ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ} : ψ g = 1 := by
      have : ψ ∈ Subgroup.closure
          {χ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ| IsPrimePow (orderOf χ)} := by
        rw [CommGroup.closure_isPrimePow_orderOf_eq_top isTorsion_of_finite]
        exact Subgroup.mem_top ψ
      induction this using Subgroup.closure_induction with
      | mem η hη => exact Subgroup.mem_iInf.mp hg ⟨η, hη⟩
      | one => simp
      | mul η₁ η₂ _ _ h₁ h₂ => rw [MonoidHom.mul_apply, h₁, h₂, one_mul]
      | inv η _ hη => rw [MonoidHom.inv_apply, hη, inv_eq_one]
    obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(K/F)
      (AlgebraicClosure ℚ) h
    exact hψ h_eq_one
