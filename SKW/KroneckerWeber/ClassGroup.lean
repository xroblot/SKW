module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion

public import SKW.KroneckerWeber.Basic
public import SKW.Stickelberger.Stickelberger
public import SKW.Prereqs.Action
public import SKW.Prereqs.FractionalIdeal

@[expose] public section

/-!
# Class group argument for Kronecker-Weber

Uses Stickelberger's theorem to show that if `(μ) = 𝔞ᵖ` in `𝓞_F`, then `𝔞` is principal,
hence `μ = αᵖ · η` for a unit `η ∈ 𝓞_F×`. A further unit argument shows `η` is a `p`-th power
times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`.
-/

open NumberField Ideal Polynomial Module IsCyclotomicExtension.Rat

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime] [Fact (Odd p)]
variable (L : Type*) [Field L] [NumberField L]
variable (F : IntermediateField ℚ L) [IsCyclotomicExtension {p} ℚ F]
variable {𝔞 : Ideal (𝓞 F)} {μ : 𝓞 F}

variable [IsGalois F L] [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p)
variable [hQL : IsAbelianGalois ℚ L] {μ : 𝓞 F} (hμ : μ ≠ 0)
  [hS : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))]
  (hIrr:  Irreducible (X ^ p - C ((algebraMap (𝓞 F) F) μ)))

set_option maxHeartbeats 500000 in
include hrF hIrr in
open Pointwise nonZeroDivisors FractionalIdeal in
/-- By Stickelberger's theorem, if `(μ) = 𝔞ᵖ` then the ideal class `[𝔞]` is trivial. -/
lemma kw_class_trivial (h𝔞 : 𝔞 ^ p = span {μ}) : 𝔞.IsPrincipal := by
  have : IsGalois ℚ F := sorry
  let 𝔞₀ : (Ideal (𝓞 F))⁰ := ⟨𝔞, sorry⟩
  have h₁ {a : (ZMod p)ˣ} : ClassGroup.mk0 ((galEquivZMod p F).symm a • 𝔞₀) =
      ClassGroup.mk0 (𝔞₀ ^ a.val.val) := by
    rw [eq_comm, ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring F]
    obtain ⟨ξ, hξ₀, hξ⟩ := kw_abelian_kummer p L F hrF hIrr ((galEquivZMod p F).symm a)
    rw [MulEquiv.apply_symm_apply] at hξ
    refine ⟨ξ, hξ₀, ?_⟩
    rw [← (IsMulTorsionFree.pow_left_injective hp.out.ne_zero).eq_iff, mul_pow]
    rw [SubmonoidClass.coe_pow, ← coeIdeal_pow, pow_right_comm, h𝔞, coeIdeal_pow,
      coeIdeal_span_singleton, spanSingleton_pow, spanSingleton_pow, spanSingleton_mul_spanSingleton,
      ← hξ, ← coeIdeal_pow, val_smul, ← smul_pow', h𝔞, smul_span, coeIdeal_span_singleton,
      algebraMap.smul', AlgEquiv.smul_def]
  have h₂ := Stickelberger F p 
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
