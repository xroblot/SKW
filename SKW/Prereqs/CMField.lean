module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

open NumberField IsCMField Units

@[expose] public section

/-! ### Units of a CM field -/

section Units

namespace NumberField.IsCMField

variable {K : Type*} [Field K]

theorem exists_torsion_realunits_pow_indexRealUnits_eq_mul (u : (𝓞 K)ˣ) :
    ∃ ζ : Units.torsion K, ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧ u ^ indexRealUnits K = ζ * v := by
  obtain ⟨⟨v, hv⟩, ζ, h⟩ := Subgroup.mem_sup'.mp <| Subgroup.pow_index_mem (realUnits K ⊔ torsion K) u
  exact ⟨ζ, v, hv, by rwa [eq_comm, mul_comm]⟩

variable [CharZero K] [IsCMField K] [NumberField K]

theorem exists_torsion_realunits_pow_two_eq_mul (u : (𝓞 K)ˣ) :
    ∃ ζ : Units.torsion K, ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧ u ^ 2 = ζ * v := by
  obtain ⟨ζ, v, hv, h⟩ := exists_torsion_realunits_pow_indexRealUnits_eq_mul u
  obtain (hi | hi) := indexRealUnits_eq_one_or_two K
  · refine ⟨ζ ^ 2, v ^ 2, Subgroup.pow_mem (realUnits K) hv 2, ?_⟩
    rw [SubmonoidClass.coe_pow, ← mul_pow, ← h, hi, pow_one]
  · exact ⟨ζ, v, hv, by rwa [← hi]⟩

/-- The `Units.val` of `unitsComplexConj` is `ringOfIntegersComplexConj` of the `Units.val`. -/
@[simp]
theorem coe_unitsComplexConj {K : Type*} [Field K] [CharZero K] [IsCMField K]
    [Algebra.IsIntegral ℚ K] (u : (𝓞 K)ˣ) :
    (unitsComplexConj K u).val = ringOfIntegersComplexConj K u.val := rfl

end NumberField.IsCMField

end Units

/-! ### Conjugation and roots of unity -/

section RootsOfUnity

/-- A complex-conjugation-type automorphism sends a root of unity to its inverse. -/
theorem NumberField.ComplexEmbedding.IsConj.eq_inv_of_pow_eq_one {K : Type*} [Field K]
    {k : Type*} [Field k] [Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)}
    (hσ : IsConj φ σ) {ζ : K} {n : ℕ} [NeZero n] (hζ : ζ ^ n = 1) :
    σ ζ = ζ⁻¹ := by
  apply φ.injective
  rw [IsConj.eq hσ, RCLike.star_def, ← Complex.inv_eq_conj, map_inv₀]
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) (NeZero.ne n)

/-- A complex-conjugation-type automorphism sends a primitive root of unity to its inverse. -/
theorem NumberField.ComplexEmbedding.IsConj.eq_inv_of_isPrimitiveRoot {K : Type*} [Field K]
    {k : Type*} [Field k] [Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)}
    (hσ : IsConj φ σ) {ζ : K} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    σ ζ = ζ⁻¹ :=
  hσ.eq_inv_of_pow_eq_one hζ.pow_eq_one

/-- Complex conjugation of a CM field sends a primitive root of unity to its inverse. This is the
version of `NumberField.IsCMField.complexConj_torsion` for an arbitrary primitive root. -/
theorem NumberField.IsCMField.complexConj_eq_inv_of_isPrimitiveRoot {K : Type*} [Field K]
    [NumberField K] [IsCMField K] {ζ : K} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    complexConj K ζ = ζ⁻¹ :=
  (isConj_complexConj K
    (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))).eq_inv_of_isPrimitiveRoot hζ

end RootsOfUnity

/-! ### `Gal(K/ℚ) ⧸ ⟨c⟩` is a Galois group for `K⁺/ℚ` -/

section CMGaloisGroup

namespace NumberField.IsCMField

noncomputable section

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/-- Complex conjugation of the CM field `K`, as an element of `Gal(K/ℚ)`. -/
noncomputable def ratComplexConj : Gal(K/ℚ) :=
  (complexConj K).restrictScalars ℚ

@[simp]
theorem ratComplexConj_apply (x : K) : ratComplexConj K x = complexConj K x := rfl

def zpowersRatComplexConjEquiv :
    Subgroup.zpowers (complexConj K) ≃* Subgroup.zpowers (ratComplexConj K) :=
  (Subgroup.equivMapOfInjective _ (AlgEquiv.restrictScalarsHom ℚ)
    (AlgEquiv.restrictScalars_injective ℚ)).trans
      (MulEquiv.subgroupCongr (MonoidHom.map_zpowers _ _))

variable {K}

theorem zpowersRatComplexConjEquiv_smul (σ : Subgroup.zpowers (complexConj K)) (x : K) :
    zpowersRatComplexConjEquiv K σ • x = σ • x := rfl

theorem zpowersRatComplexConjEquiv_symm_smul (σ : Subgroup.zpowers (ratComplexConj K)) (x : K) :
    ((zpowersRatComplexConjEquiv K).symm σ) • x = σ • x := by
  simp [← zpowersRatComplexConjEquiv_smul]

instance : IsGaloisGroup (Subgroup.zpowers (ratComplexConj K)) K⁺ K :=
  IsGaloisGroup.of_mulEquiv
    (((zpowersRatComplexConjEquiv K).symm.trans
      (MulEquiv.subgroupCongr (zpowers_complexConj_eq_top K))).trans Subgroup.topEquiv)
    fun σ y ↦ by simpa [MulAction.subgroup_smul_def] using zpowersRatComplexConjEquiv_symm_smul σ y

/-- Complex conjugation, as an element of `Gal(K/ℚ)`, is the conjugation of any complex
embedding of `K`. -/
theorem isConj_ratComplexConj (φ : K →+* ℂ) : ComplexEmbedding.IsConj φ (ratComplexConj K) :=
  isConj_complexConj K φ

/-- Any conjugation in `Gal(K/ℚ)` is the complex conjugation of the CM field `K`. -/
theorem eq_ratComplexConj {φ : K →+* ℂ} {σ : Gal(K/ℚ)} (hσ : ComplexEmbedding.IsConj φ σ) :
    σ = ratComplexConj K :=
  hσ.ext (isConj_ratComplexConj φ)

variable (K)

/-- Complex conjugation has order `2` in `Gal(K/ℚ)`. -/
theorem orderOf_ratComplexConj : orderOf (ratComplexConj K) = 2 :=
  (orderOf_injective (AlgEquiv.restrictScalarsHom ℚ)
    (AlgEquiv.restrictScalars_injective ℚ) (complexConj K)).trans (orderOf_complexConj K)

/-- Complex conjugation is central in `Gal(K/ℚ)`. -/
theorem ratComplexConj_mem_center : ratComplexConj K ∈ Subgroup.center Gal(K/ℚ) := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  refine Subgroup.mem_center_iff.mpr fun σ ↦ ?_
  rw [← _root_.eq_inv_mul_iff_mul_eq, ← mul_assoc, eq_ratComplexConj <| (isConj_ratComplexConj φ).comp σ]

/-- The subgroup generated by complex conjugation is normal in `Gal(K/ℚ)`. -/
instance : (Subgroup.zpowers (ratComplexConj K)).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (ratComplexConj_mem_center K))

/-- The quotient of `Gal(K/ℚ)` by complex conjugation acts on `K⁺`. -/
instance : MulSemiringAction (Gal(K/ℚ) ⧸ Subgroup.zpowers (ratComplexConj K)) K⁺ :=
  IsGaloisGroup.mulSemiringActionQuotient Gal(K/ℚ) K⁺ K _

instance : MulSemiringAction Gal(K/ℚ) K⁺ :=
  IsGaloisGroup.mulSemiringActionOfNormal Gal(K/ℚ) K⁺ K (Subgroup.zpowers (ratComplexConj K))

/-- The quotient of `Gal(K/ℚ)` by the subgroup generated by the complex conjugation
is a Galois group for `K⁺/ℚ`. -/
instance isGaloisGroup_quotient_ratComplexConj [IsGalois ℚ K] :
    IsGaloisGroup (Gal(K/ℚ) ⧸ Subgroup.zpowers (ratComplexConj K)) ℚ K⁺ :=
  IsGaloisGroup.quotient Gal(K/ℚ) ℚ K⁺ K _

/-- The maximal real subfield of a CM field Galois over `ℚ` is Galois over `ℚ`. -/
instance [IsGalois ℚ K] : IsGalois ℚ K⁺ :=
  IsGaloisGroup.isGalois (Gal(K/ℚ) ⧸ Subgroup.zpowers (ratComplexConj K)) ℚ K⁺

end

/-! ### Complex conjugation and subfields -/

section Subfields

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [IsCMField K]
  [IsCMField L] [Algebra K L]

/-- The complex conjugations of two CM fields `K ⊆ L` commute with the inclusion. -/
theorem ratComplexConj_algebraMap (x : K) :
    ratComplexConj L (algebraMap K L x) = algebraMap K L (ratComplexConj K x) := by
  let φ : L →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  rw [ComplexEmbedding.IsConj.eq (isConj_ratComplexConj φ)]
  exact (ComplexEmbedding.IsConj.eq (isConj_ratComplexConj (φ.comp (algebraMap K L))) x).symm

/-- For an extension `L/K` of CM fields with `K/ℚ` normal, the restriction of the complex
conjugation of `L` to `K` is the complex conjugation of `K`. -/
theorem restrictNormal_ratComplexConj [Normal ℚ K] :
    (ratComplexConj L).restrictNormal K = ratComplexConj K :=
  AlgEquiv.ext fun x ↦ (algebraMap K L).injective <| by
    rw [AlgEquiv.restrictNormal_commutes, ratComplexConj_algebraMap]

/-- Version of `restrictNormal_ratComplexConj` for `AlgEquiv.restrictNormalHom`. -/
theorem restrictNormalHom_ratComplexConj [Normal ℚ K] :
    AlgEquiv.restrictNormalHom K (ratComplexConj L) = ratComplexConj K :=
  restrictNormal_ratComplexConj

end Subfields

end NumberField.IsCMField

end CMGaloisGroup
