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

open IntermediateField in
/-- `lift` preserves the rank over the base field. -/
theorem IntermediateField.rank_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} (E : IntermediateField K F) :
    Module.rank K (lift E) = Module.rank K E :=
  (liftAlgEquiv E).toLinearEquiv.rank_eq.symm

open IntermediateField in
/-- `lift` preserves the degree over the base field: `[lift E : K] = [E : K]`. -/
theorem IntermediateField.finrank_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} (E : IntermediateField K F) :
    Module.finrank K (lift E) = Module.finrank K E :=
  (liftAlgEquiv E).toLinearEquiv.finrank_eq.symm

open IntermediateField in
/-- `lift` preserves finite-dimensionality over the base field. -/
instance IntermediateField.finiteDimensional_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} {E : IntermediateField K F} [FiniteDimensional K E] :
    FiniteDimensional K (lift E) :=
  Module.Finite.equiv (liftAlgEquiv E).toLinearEquiv

open IntermediateField in
/-- `restrict` preserves the rank over the base field. -/
theorem IntermediateField.rank_restrict {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F E : IntermediateField K L} (h : F ≤ E) :
    Module.rank K (restrict h) = Module.rank K F :=
  (restrict_algEquiv h).toLinearEquiv.rank_eq.symm

open IntermediateField in
/-- `restrict` preserves the degree over the base field: `[restrict h : K] = [F : K]`. -/
theorem IntermediateField.finrank_restrict {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F E : IntermediateField K L} (h : F ≤ E) :
    Module.finrank K (restrict h) = Module.finrank K F :=
  (restrict_algEquiv h).toLinearEquiv.finrank_eq.symm

open IntermediateField in
/-- `restrict` preserves finite-dimensionality over the base field. -/
instance IntermediateField.finiteDimensional_restrict {K L : Type*} [Field K] [Field L]
    [Algebra K L] {F E : IntermediateField K L} {h : F ≤ E} [FiniteDimensional K F] :
    FiniteDimensional K (restrict h) :=
  Module.Finite.equiv (restrict_algEquiv h).toLinearEquiv

open IntermediateField in
/-- `restrict` is order-reflecting in the restricted field: for `F₁, F₂ ≤ E`, one has
`restrict h₁ ≤ restrict h₂` iff `F₁ ≤ F₂`. -/
theorem IntermediateField.restrict_le_restrict_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F₁ F₂ E : IntermediateField K L} (h₁ : F₁ ≤ E) (h₂ : F₂ ≤ E) :
    restrict h₁ ≤ restrict h₂ ↔ F₁ ≤ F₂ :=
  ⟨fun hle x hx ↦ (mem_restrict h₂ ⟨x, h₁ hx⟩).1 (hle ((mem_restrict h₁ ⟨x, h₁ hx⟩).2 hx)),
   fun hF x hx ↦ (mem_restrict h₂ x).2 (hF ((mem_restrict h₁ x).1 hx))⟩

open IntermediateField in
/-- `lift` is order-reflecting: `lift E₁ ≤ lift E₂` iff `E₁ ≤ E₂`. -/
theorem IntermediateField.lift_le_lift_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} {E₁ E₂ : IntermediateField K F} :
    lift E₁ ≤ lift E₂ ↔ E₁ ≤ E₂ :=
  ⟨fun hle x hx ↦ (mem_lift x).1 (hle ((mem_lift x).2 hx)),
   fun hE _ hx ↦ by obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, hE hy, rfl⟩⟩

@[simp]
theorem IsGaloisGroup.finrank_fixedPoints_eq_index_subgroup (G K L : Type*) [Group G] [Field K]
    [Field L] [Algebra K L] [MulSemiringAction G L] (H : Subgroup G) [Finite H]
    [IsGaloisGroup G K L] :
    Module.finrank K ↑(FixedPoints.intermediateField H : IntermediateField K L) = H.index := by
  have : Module.finrank ↑(FixedPoints.intermediateField H : IntermediateField K L) L ≠ 0 := by
    rw [finrank_fixedPoints_eq_card_subgroup]
    exact Nat.card_pos.ne'
  rw [← mul_left_inj' this, Module.finrank_mul_finrank, finrank_fixedPoints_eq_card_subgroup,
    Subgroup.index_mul_card, card_eq_finrank G K L]

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

open IntermediateField Module in
/-- If `B / F` is a finite Galois extension and the compositum `A ⊔ B` is all of `E`, then the
relative degree `[E : A]` divides `[B : F]`. This is the ⊤-case: here `E` is genuinely an
`↥A`-algebra, so the divisibility can be stated directly (unlike the general compositum form
`finrank_sup_dvd_mul_of_isGalois`). It follows from the injection `Gal(E/A) ↪ Gal(B/F)` induced by
restriction and Lagrange's theorem. -/
theorem IntermediateField.finrank_dvd_finrank_of_isGalois_of_sup_eq_top {F E : Type*} [Field F]
    [Field E] [Algebra F E] (A B : IntermediateField F E)
    [FiniteDimensional A E] [FiniteDimensional F B] [IsGalois F B] (h : B ⊔ A = ⊤) :
    finrank A E ∣ finrank F B := by
  have : IsGalois A E := IsGalois.sup_right B A h
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_dvd_of_injective _ <| restrictRestrictAlgEquivMapHom_injective B A h

open Module in
/-- If `B / F` is a finite Galois extension, then for any finite `A`, the degree of the compositum
`A ⊔ B` over `F` divides `[A : F] * [B : F]`. (Equivalently, `[A ⊔ B : A] ∣ [B : F]`, which fails
without the Galois hypothesis on `B`.)

Remark: we cannot state this as `finrank A ↥(A ⊔ B) ∣ finrank F ↥B` since `↥(A ⊔ B)` is not, by
default, an `↥A`-algebra; hence the product form `[A ⊔ B : F] ∣ [A : F] * [B : F]`. The ⊤-case
`finrank_dvd_finrank_of_isGalois_of_sup_eq_top` does not have this obstruction. -/
theorem IntermediateField.finrank_sup_dvd_mul_of_isGalois {F E : Type*} [Field F] [Field E]
    [Algebra F E] (A B : IntermediateField F E) [FiniteDimensional F A] [IsGalois F B]
    [FiniteDimensional F B] :
    finrank F ↑(A ⊔ B) ∣ finrank F A * finrank F B := by
  let A' : IntermediateField F ↥(A ⊔ B) := A.restrict le_sup_left
  let B' : IntermediateField F ↥(A ⊔ B) := B.restrict le_sup_right
  have : IsGalois F B' := IsGalois.of_algEquiv (restrict_algEquiv le_sup_right)
  have : B' ⊔ A' = ⊤ :=
    lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_top, sup_comm])
  have := mul_dvd_mul_left (finrank F A') <| finrank_dvd_finrank_of_isGalois_of_sup_eq_top A' B' this
  rwa [finrank_mul_finrank, finrank_restrict, finrank_restrict] at this

theorem IntermediateField.lift_iInf {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (L : ι → IntermediateField F K) :
    lift (⨅ i ∈ S, L i) = ⨅ i ∈ S, lift (L i) := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s h hs hi =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert, Finset.iInf_insert, lift_inf, hi]

theorem IntermediateField.lift_iSup (F E : Type*) [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) {ι : Type*} (S : Finset ι) (L : ι → IntermediateField F K) :
    lift (⨆ i ∈ S, L i) = ⨆ i ∈ S, lift (L i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i s _ hi => rw [Finset.iSup_insert, Finset.iSup_insert, lift_sup, hi]
