module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.NumberTheory.NumberField.CMField

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

variable (p : ℕ)
variable (L : Type*) [Field L] [NumberField L]
variable (F : IntermediateField ℚ L)
variable {𝔞 : Ideal (𝓞 F)} {μ : 𝓞 F}

/-- If `𝔞` is principal, `μ = αᵖ · η` for some `α ∈ 𝓞_F` and unit `η ∈ 𝓞_F×`. -/
lemma kw_mu_unit (h𝔞₀ : 𝔞 ≠ ⊥) (h𝔞 : span {μ} = 𝔞 ^ p) (hcl : 𝔞.IsPrincipal) :
    ∃ (α : 𝓞 F) (η : (𝓞 F)ˣ), μ = α ^ p * η := by
  obtain ⟨α, rfl⟩ := hcl
  rw [span_singleton_pow, span_singleton_eq_span_singleton, Associated.comm] at h𝔞
  obtain ⟨η, hη⟩ := h𝔞
  exact ⟨α, η, hη.symm⟩

variable [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ F] [IsGalois F L]
variable [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p)
variable [hQL : IsAbelianGalois ℚ L] {μ : 𝓞 F} (hμ : μ ≠ 0)
  [hS : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))]
  (hIrr:  Irreducible (X ^ p - C ((algebraMap (𝓞 F) F) μ)))

include hrF hIrr in
open Pointwise nonZeroDivisors FractionalIdeal in
/-- By Stickelberger's theorem, if `(μ) = 𝔞ᵖ` then the ideal class `[𝔞]` is trivial. -/
lemma kw_class_trivial (h𝔞₀ : 𝔞 ≠ ⊥) (h𝔞 : 𝔞 ^ p = span {μ}) : 𝔞.IsPrincipal := by
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {p} ℚ ↥F
  let 𝔞₀ : (Ideal (𝓞 F))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞₀⟩
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero h𝔞₀)]
  change ClassGroup.mk0 𝔞₀ = 1
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
  have h₃ := Stickelberger p F (ClassGroup.mk0 𝔞₀)
  have h₂ : ClassGroup.mk0 𝔞₀ ^ p = 1 := by
    rw [← map_pow, ClassGroup.mk0_eq_one_iff]
    exact ⟨μ, h𝔞⟩
  have h₄ {a : (ZMod p)ˣ} :
      ClassGroup.mk0 𝔞₀ ^ (a⁻¹.val.val * a.val.val) = ClassGroup.mk0 𝔞₀ := by
    rw [pow_eq_pow_mod _ h₂, ← ZMod.val_mul, Units.inv_mul, ZMod.val_one, pow_one]
  simp_rw [← map_inv, ClassGroup.smul_mk0, h₁, map_pow, ← pow_mul, h₄] at h₃
  rw [Finset.prod_const, Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h₃
  have h₅ := h₂.trans h₃.symm
  rwa [← zpow_natCast, ← zpow_natCast, ← orderOf_dvd_sub_iff_zpow_eq_zpow, Nat.cast_sub hp.out.one_le,
    Nat.cast_one, sub_sub_cancel, Int.natCast_dvd_ofNat, Nat.dvd_one, orderOf_eq_one_iff] at h₅

/-- The unit `η` is a `p`-th power times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`. -/
lemma kw_unit_root_of_unity (hp' : Odd p) (K : IntermediateField ℚ L) [IsGalois ℚ K]
    [IsCyclic (K ≃ₐ[ℚ] K)] (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p)
    (hL : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))) (h𝔞₀ : 𝔞 ≠ ⊥)
    (h𝔞 : span {μ} = 𝔞 ^ p) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  have : IsCMField F :=
    IsCyclotomicExtension.Rat.isCMField F (S := {p}) <|
      exists_eq_left.mpr <| (Nat.Prime.odd_iff hp.out).mp hp'
  
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
