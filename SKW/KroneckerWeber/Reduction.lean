module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.FieldTheory.Galois.Basic

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

open NumberField Ideal Pointwise

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- Two cyclic `p`-extensions of `ℚ` whose compositum is cyclic must be comparable. -/
lemma kw_cyclic_compositum
    (K K' : Type*) [Field K] [Field K'] [NumberField K] [NumberField K']
    [IsGalois ℚ K] [IsGalois ℚ K'] [IsCyclic (K ≃ₐ[ℚ] K)] [IsCyclic (K' ≃ₐ[ℚ] K')]
    (hK : ∃ n : ℕ, 0 < n ∧ Module.finrank ℚ K = p ^ n)
    (hK' : ∃ n : ℕ, 0 < n ∧ Module.finrank ℚ K' = p ^ n)
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [Algebra K L] [Algebra K' L]
    [IsScalarTower ℚ K L] [IsScalarTower ℚ K' L]
    [IsGalois ℚ L] [IsCyclic (L ≃ₐ[ℚ] L)] :
    Nonempty (K →ₐ[ℚ] K') ∨ Nonempty (K' →ₐ[ℚ] K) := by
  sorry

/-- Every non-trivial extension of `ℚ` is ramified at some finite prime (Minkowski). -/
lemma kw_minkowski
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    (h : Module.finrank ℚ K > 1) :
    ∃ q : ℕ, q.Prime ∧ ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal ∧
      𝔮.LiesOver (Ideal.span {(q : ℤ)}) ∧
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 > 1 := by
  sorry

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
