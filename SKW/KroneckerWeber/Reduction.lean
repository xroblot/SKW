module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.Algebra.IsPrimePow

public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.Ideals

@[expose] public section

/-!
# Reduction steps for Kronecker-Weber

This file establishes the reduction steps that allow us to prove Kronecker-Weber by induction:

1. `kw_cyclic_compositum`: If two cyclic `p`-extensions have cyclic compositum, one contains the
   other.
2. `kw_minkowski`: Every non-trivial extension of `ℚ` is ramified at some finite prime.
3. `kw_ramification_reduction`: Given `K/ℚ` cyclic of prime power degree with `q ≠ p` ramified,
   there exists a cyclotomic `L/ℚ` such that `KL = FL` for `F/ℚ` cyclic of prime power degree
   with `q` unramified.

The decomposition of a finite abelian extension into cyclic prime power subextensions is
`IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top` (in `SKW/Prereqs/IntermediateFields.lean`).
The reduction of the general (abelian) case to the cyclic prime power case
(`kw_reduce_to_prime_power`) lives in `KroneckerWeber.lean`, in `IntermediateField ℚ A` currency.
-/



open NumberField Ideal Pointwise Module IntermediateField

noncomputable section

/-- `K/ℚ` is a cyclic Galois extension of prime power degree (`> 1`). -/
def IsCyclicOfPrimePowDegree (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  IsGalois ℚ K ∧ IsCyclic Gal(K/ℚ) ∧ IsPrimePow (Module.finrank ℚ K)

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
there exist `r > 0` and a cyclic `F/ℚ` of degree `pᵐ` (in the same ambient field `A`), unramified
at `q` and not ramified at any prime where `K` is unramified, such that `K · ℚ(ζ_{qʳ}) = F · ℚ(ζ_{qʳ})`.
This removes `q` from the set of ramified primes at the cost of a `q`-power cyclotomic factor. -/
lemma kw_ramification_reduction {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A)
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (m : ℕ) (hm : 0 < m) (hK : Module.finrank ℚ K = p ^ m)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (hram : ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (r : ℕ),
      0 < r ∧ IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ Module.finrank ℚ F = p ^ m ∧
      Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)}) ∧
      (∀ q' : ℕ, q'.Prime → Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q' : ℤ)}) →
        Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q' : ℤ)})) ∧
      K ⊔ ℚ⟮ξ (q ^ r)⟯ = F ⊔ ℚ⟮ξ (q ^ r)⟯ := by
  sorry

end

end
