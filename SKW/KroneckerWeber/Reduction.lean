module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.ExistsRamified

public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.Ideals

@[expose] public section

/-!
# Reduction steps for Kronecker-Weber

This file establishes the reduction steps that allow us to prove Kronecker-Weber by induction:

1. `kw_abelian_cyclic_decomp`: Every finite abelian extension of `ℚ` is the compositum of cyclic
   extensions of prime power degree.
2. `kw_cyclic_compositum`: If two cyclic `p`-extensions have cyclic compositum, one contains the
   other.
3. `kw_minkowski`: Every non-trivial extension of `ℚ` is ramified at some finite prime.
4. `kw_ramification_reduction`: Given `K/ℚ` cyclic of prime power degree with `q ≠ p` ramified,
   there exists a cyclotomic `L/ℚ` such that `KL = FL` for `F/ℚ` cyclic of prime power degree
   with `q` unramified.
5. `kw_reduce_to_prime_power`: It suffices to prove KW for cyclic prime power degree extensions
   unramified outside `p`.
-/

open NumberField Ideal Pointwise Module

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- Two cyclic `p`-extensions of `ℚ` whose compositum is cyclic must be comparable. -/
lemma kw_cyclic_compositum (L : Type*) [Field L] [NumberField L] (K K' : IntermediateField ℚ L)
    (h : finrank ℚ K ∣ finrank ℚ K') [IsGalois ℚ L] [hCL : IsCyclic (L ≃ₐ[ℚ] L)] :
    K ≤ K' := by
  rw [← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/ℚ) ℚ L K,
    ← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/ℚ) ℚ L K']
  apply IsGaloisGroup.fixedPoints_le_of_le
  rw [IsCyclic.subgroup_le_subgroup_iff, IsGaloisGroup.card_fixingSubgroup_eq_finrank,
    IsGaloisGroup.card_fixingSubgroup_eq_finrank]
  have hd : finrank ℚ K ∣ finrank ℚ L := finrank_mul_finrank ℚ K L ▸ dvd_mul_right _ _
  have hd' : finrank ℚ K' ∣ finrank ℚ L := finrank_mul_finrank ℚ K' L ▸ dvd_mul_right _ _
  have he : finrank K L = finrank ℚ L / finrank ℚ K :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  have he' : finrank K' L = finrank ℚ L / finrank ℚ K' :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  rwa [he, he', Nat.div_dvd_div_iff finrank_pos finrank_pos hd' hd]

/-- Every non-trivial extension of `ℚ` is ramified at some finite prime (Minkowski). -/
lemma kw_minkowski
    (K : Type*) [Field K] [NumberField K]
    (h : Module.finrank ℚ K > 1) :
    ∃ q : ℕ, q.Prime ∧ ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal ∧
      𝔮.LiesOver (Ideal.span {(q : ℤ)}) ∧
      1 < Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 := by
  obtain ⟨𝔮, hq, hq'⟩ := exists_not_isUnramifiedAt_int (K := K) (𝒪 := 𝓞 K) h.ne'
  refine ⟨absNorm (Ideal.under ℤ 𝔮), Nat.absNorm_under_prime 𝔮, 𝔮, hq, Int.liesOver_span_absNorm 𝔮, ?_⟩
  rwa [Int.ideal_span_absNorm_eq_self, ← Algebra.not_isUnramifiedAt_iff_of_isDedekindDomain]
  exact IsMaximal.ne_bot_of_isIntegral_int 𝔮

/-- Ramification reduction: given `K/ℚ` cyclic of prime power degree `pᵐ` with `q ≠ p` ramified,
there exists a cyclotomic extension `L/ℚ` such that `KL = FL` for some cyclic `F/ℚ` of degree
`pᵐ` in which `q` is unramified. -/
lemma kw_ramification_reduction
    (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
    (m : ℕ) (hm : 0 < m) (hK : Module.finrank ℚ K = p ^ m)
    (q : ℕ) [hq : Fact q.Prime] (hqp : q ≠ p)
    (hram : ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal ∧ 𝔮.LiesOver (Ideal.span {(q : ℤ)}) ∧
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 > 1) :
    ∃ (F : Type*) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F) (_ : IsCyclic (F ≃ₐ[ℚ] F))
      (_ : Module.finrank ℚ F = p ^ m)
      (hFram : ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal → 𝔮.LiesOver (Ideal.span {(q : ℤ)}) →
        Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 = 1)
      (r : ℕ) (hr : 0 < r) (Λ : Type*) (_ : Field Λ) (_ : NumberField Λ)
      (_ : IsCyclotomicExtension {q ^ r} ℚ Λ),
      True := by -- placeholder; compositum KΛ = FΛ
  sorry

/-- Main reduction: it suffices to prove KW for cyclic prime power degree extensions of `ℚ`
unramified outside `p`. -/
theorem kw_reduce_to_prime_power :
    (∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 0 < m)
      (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
      (hK : Module.finrank ℚ K = p ^ m)
      (hram : ∀ q : ℕ, q.Prime → q ≠ p →
        ∀ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal → 𝔮.LiesOver (Ideal.span {(q : ℤ)}) →
        Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 = 1),
      ∃ r : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField (p ^ r) ℚ)) →
    ∀ (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]
      [∀ σ τ : K ≃ₐ[ℚ] K, Decidable (σ * τ = τ * σ)],
      ∃ n : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  sorry

end

end
