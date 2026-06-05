module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RootsOfUnity.Basic

public import SKW.KroneckerWeber.KummerCriterion

@[expose] public section

/-!
# Basic setup for the Kronecker-Weber theorem

Let `p` be an odd prime and `K/ℚ` a cyclic extension of degree `p` unramified outside `p`.
Set `F = ℚ(ζ_p)` and `L = KF`.

This file establishes:
- `kw_kummer`: `L/F` is a Kummer extension `F(ᵖ√μ)` for some `μ ∈ 𝓞_F`, unramified outside `p`.
- `kw_abelian_kummer`: The Kummer criterion for `L/ℚ` to be abelian.
- `kw_split_prime`: Primes `𝔮` with `p ∤ v_𝔮(μ)` split completely in `F/ℚ`.
- `kw_mu_val_p`: For every prime `𝔮` of `F`, `p ∣ v_𝔮(μ)`.
- `kw_mu_pth_power_ideal`: `(μ) = 𝔞ᵖ` for some ideal `𝔞` of `𝓞_F`.
-/

open NumberField Ideal Polynomial Pointwise

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
variable (L : Type*) [Field L] [NumberField L]
  [Algebra ℚ L] [Algebra F L] [Algebra K L]
  [IsScalarTower ℚ F L] [IsScalarTower ℚ K L] [IsGalois ℚ L]

/-- `K/ℚ` is unramified outside `p`: every prime `q ≠ p` has ramification index 1 in `K`. -/
def UnramifiedOutside (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ p →
    ∀ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal → 𝔮.LiesOver (span {(q : ℤ)}) →
      Ideal.ramificationIdx (span {(q : ℤ)}) 𝔮 = 1

/-- `L/F` is a Kummer extension: there exists `μ ∈ 𝓞_F` such that `L = F(ᵖ√μ)` and `L/F`
is unramified outside `p`. -/
lemma kw_kummer
    (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p) :
    ∃ μ : 𝓞 F, μ ≠ 0 ∧
      IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ)) ∧
      UnramifiedOutside L p := by
  sorry

variable {μ : 𝓞 F} (hμ : μ ≠ 0)
  (hL : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ)))

/-- The abelianity criterion for the Kummer extension `L = F(ᵖ√μ)` over `ℚ`. -/
lemma kw_abelian_kummer :
    ∀ σ : F ≃ₐ[ℚ] F, ∃ (ξ : F) (a : ℤ),
      σ (algebraMap (𝓞 F) F μ) = ξ ^ p * (algebraMap (𝓞 F) F μ) ^ a := by
  sorry

/-- If `𝔮` is a prime of `𝓞_F` with `p ∤ v_𝔮(μ)` and `L/ℚ` is abelian, then `𝔮` splits
completely in `F/ℚ`: every `σ ∈ Gal(F/ℚ)` with `σ • 𝔮 = 𝔮` is the identity. -/
lemma kw_split_prime (𝔮 : Ideal (𝓞 F)) [h𝔮 : 𝔮.IsMaximal]
    (hv : ¬ (p : ℕ) ∣ (emultiplicity 𝔮 (span {(μ : 𝓞 F)})).toNat) :
    ∀ σ : F ≃ₐ[ℚ] F, σ • 𝔮 = 𝔮 → σ = AlgEquiv.refl := by
  sorry

/-- For every prime `𝔮` of `𝓞_F`, `p ∣ v_𝔮(μ)`. -/
lemma kw_mu_val_p (𝔮 : Ideal (𝓞 F)) [𝔮.IsMaximal] :
    (p : ℕ) ∣ (emultiplicity 𝔮 (span {(μ : 𝓞 F)})).toNat := by
  sorry

/-- The ideal `(μ)` is a `p`-th power: `(μ) = 𝔞ᵖ` for some ideal `𝔞` of `𝓞_F`, and moreover
`(1 - ζ_p) ∤ 𝔞`. -/
lemma kw_mu_pth_power_ideal :
    ∃ 𝔞 : Ideal (𝓞 F), span {(μ : 𝓞 F)} = 𝔞 ^ p ∧
      ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → 𝔭.LiesOver (span {(p : ℤ)}) → ¬ 𝔭 ∣ 𝔞 := by
  sorry

end

end
