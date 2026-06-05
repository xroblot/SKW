module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

public import SKW.KroneckerWeber.Basic
public import SKW.Stickelberger.Stickelberger

@[expose] public section

/-!
# Class group argument for Kronecker-Weber

Uses Stickelberger's theorem to show that if `(μ) = 𝔞ᵖ` in `𝓞_F`, then `𝔞` is principal,
hence `μ = αᵖ · η` for a unit `η ∈ 𝓞_F×`. A further unit argument shows `η` is a `p`-th power
times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`.
-/

open NumberField Ideal Polynomial

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime] [Fact (Odd p)]
variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]
variable {𝔞 : Ideal (𝓞 F)} {μ : 𝓞 F}

/-- By Stickelberger's theorem, if `(μ) = 𝔞ᵖ` then the ideal class `[𝔞]` is trivial. -/
lemma kw_class_trivial (h𝔞 : span {μ} = 𝔞 ^ p) : 𝔞.IsPrincipal := by
  sorry

/-- Since `𝔞` is principal, `μ = αᵖ · η` for some `α ∈ 𝓞_F` and unit `η ∈ 𝓞_F×`. -/
lemma kw_mu_unit (h𝔞 : span {μ} = 𝔞 ^ p) (hcl : 𝔞.IsPrincipal) :
    ∃ (α : 𝓞 F) (η : (𝓞 F)ˣ), μ = α ^ p * η := by
  sorry

/-- The unit `η` is a `p`-th power times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`. -/
lemma kw_unit_root_of_unity
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
    (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p)
    (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] [Algebra F L] [Algebra K L]
    [IsScalarTower ℚ F L] [IsScalarTower ℚ K L] [IsGalois ℚ L]
    (hL : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ)))
    (h𝔞 : span {μ} = 𝔞 ^ p) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  sorry

/-- Every cyclic extension of `ℚ` of prime degree `p` (odd) unramified outside `p` is contained
in the unique subfield of degree `p` of `ℚ(ζ_{p²})`. -/
theorem prop_kw_exponent_p
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
    (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p) :
    Nonempty (K →ₐ[ℚ] CyclotomicField (p ^ 2) ℚ) := by
  sorry

end

end
