module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

open NumberField IsCMField Units

@[expose] public section

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
