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
public import SKW.Prereqs.CMField

@[expose] public section

/-!
# Class group argument for Kronecker-Weber

Uses Stickelberger's theorem to show that if `(μ) = 𝔞ᵖ` in `𝓞_F`, then `𝔞` is principal,
hence `μ = αᵖ · η` for a unit `η ∈ 𝓞_F×`. A further unit argument shows `η` is a `p`-th power
times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`.
-/

open NumberField Ideal Polynomial Module IsCyclotomicExtension.Rat

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [Field L] [NumberField L]
variable (F : IntermediateField ℚ L)
variable {𝔞 : Ideal (𝓞 F)} {μ : 𝓞 F}

/-- If `𝔞` is principal, `μ = αᵖ · η` for some `α ∈ 𝓞_F` and unit `η ∈ 𝓞_F×`. -/
lemma kw_mu_unit (hμ : μ ≠ 0) (h𝔞₀ : 𝔞 ≠ ⊥) (h𝔞 : 𝔞 ^ p = span {μ}) (hcl : 𝔞.IsPrincipal) :
    ∃ (α : 𝓞 F) (η : (𝓞 F)ˣ), α ≠ 0 ∧ μ = α ^ p * η := by
  obtain ⟨α, rfl⟩ := hcl
  rw [span_singleton_pow, span_singleton_eq_span_singleton] at h𝔞
  obtain ⟨η, hη⟩ := h𝔞
  refine ⟨α, η, ?_, hη.symm⟩
  contrapose! hμ
  rw [← hη, hμ, zero_pow hp.out.ne_zero, zero_mul]

variable [IsCyclotomicExtension {p} ℚ F] [IsGalois F L]
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
    obtain ⟨ξ, hξ₀, hξ⟩ := kw_abelian_kummer p F hrF hIrr ((galEquivZMod p F).symm a)
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

set_option backward.isDefEq.respectTransparency false in
open IntermediateField Polynomial in
include hrF hIrr hμ in
/-- The unit `η` is a `p`-th power times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`. -/
lemma kw_unit_root_of_unity (hp' : Odd p) (K : IntermediateField ℚ L) [IsGalois ℚ K]
    [IsCyclic (K ≃ₐ[ℚ] K)] (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p)
    (hL : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))) (h𝔞₀ : 𝔞 ≠ ⊥)
    (h𝔞 : 𝔞 ^ p = span {μ}) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  have : IsCMField F :=
    IsCyclotomicExtension.Rat.isCMField F (S := {p}) <|
      exists_eq_left.mpr <| (Nat.Prime.odd_iff hp.out).mp hp'
  obtain ⟨α, η, hα, h⟩ := kw_mu_unit p F hμ h𝔞₀ h𝔞 (kw_class_trivial p F hrF hIrr h𝔞₀ h𝔞)
  obtain ⟨ζ, ε, hε, h'⟩ := IsCMField.exists_torsion_realunits_pow_two_eq_mul η
  have hζ : IsPrimitiveRoot (ζ.val : 𝓞 F) p := by

    sorry
  have : ∃ δ : F, δ ≠ 0 ∧ ε = δ ^ p := by
    suffices ∃ δ₀ : F, δ₀ ≠ 0 ∧ ε ^ 2 = δ₀ ^ p by
      obtain ⟨δ₀, h₀, h₁⟩ := this
      refine ⟨δ₀ ^ (Int.gcdA (2 : ℕ) p) * ε ^ (Int.gcdB (2 : ℕ) p), ?_, ?_⟩
      sorry
      rw [mul_pow, ← zpow_natCast, zpow_comm, zpow_natCast, ← h₁, ← zpow_natCast, ← zpow_mul,
        ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by simp), mul_comm _ (p : ℤ), ← Int.gcd_eq_gcd_ab,
        Int.gcd_natCast_natCast, Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hp'),
        Nat.cast_one, zpow_one]
    suffices ∃ (a : F), ∃ (b : F), b ≠ 0 ∧ a ^ p = b ^ p * ε ^ 2 by
      obtain ⟨a, b, hb₀, hab⟩ := this
      have : (algebraMap (𝓞 F) F ε) ^ 2 = (a * b⁻¹) ^ p := sorry
      refine ⟨a * b⁻¹, ?_, ?_⟩
      sorry
      rw [mul_pow, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero p hb₀), mul_comm, hab]
    obtain ⟨ξ, hξ₀, hξ⟩ : ∃ ξ, ξ ≠ 0 ∧
        (galEquivZMod p F).symm (-1) (μ : F) = ξ ^ p * (μ : F) ^ (-1 : ℤ) := by
      obtain ⟨ξ', hξ'₀, hξ'⟩ := kw_abelian_kummer p F hrF hIrr ((galEquivZMod p F).symm (-1))
      refine ⟨ξ' * μ, mul_ne_zero hξ'₀ (by simpa), ?_⟩
      rw [hξ', mul_pow, ← zpow_natCast (μ : F), ← zpow_natCast (μ : F), mul_assoc, ← zpow_add₀ (by simpa),
        MulEquiv.apply_symm_apply, show (p : ℤ) + -1 = (p - 1 : ℕ) by
          rw [Int.add_neg_one, Nat.cast_sub hp.out.one_le, Nat.cast_one],
        Units.coe_neg_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_right
    · have hε' : ((galEquivZMod p F).symm (-1)) • ε.val = ε.val := sorry
      have hζ' : ((galEquivZMod p F).symm (-1)) (ζ.val : F) = (ζ.val : F) ^ (-1 : ℤ) := sorry
      replace hξ := congr_arg ( · ^ 2) hξ
      have h₁ := congr_arg ( · ^ 2) h
      rw [mul_pow, ← Units.val_pow_eq_pow_val, h', Units.val_mul] at h₁
      have h₂ := congr_arg (algebraMap (𝓞 F) F · ) <| congr_arg ((galEquivZMod p F).symm (-1) • · ) h₁
      rwa [algebraMap.smul', AlgEquiv.smul_def, map_pow, map_pow, hξ, smul_mul', map_mul, smul_mul', hε',
        mul_pow, pow_right_comm, zpow_neg_one, inv_pow, ← map_pow, h₁, map_mul, map_mul, map_mul, mul_inv,
        mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_eq_iff_eq_mul₀ (by simp), mul_assoc, mul_assoc,
        mul_assoc, algebraMap.smul', algebraMap.smul', ← pow_two, AlgEquiv.smul_def, AlgEquiv.smul_def,
        hζ', zpow_neg_one, mul_comm (ζ.val : F)⁻¹, ← mul_assoc, ← mul_assoc, mul_left_inj' (by simp),
        pow_right_comm _ p, map_pow, ← inv_pow, ← mul_pow, map_pow _ _ p] at h₂
    · simpa
  obtain ⟨δ, hδ₀, hδ⟩ := this
  sorry
  
#exit
  have : IsSplittingField F L (X ^ p - C (ζ.val : F)) := by
    have : IsSplittingField F L (X ^ p - C (μ ^ 2 : F)) := by
      apply toto₁
      exact IsCyclotomicExtension.primitiveRoots_nonempty p ℚ F
      exact Nat.coprime_two_left.mpr hp'
    rw [h] at this
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, mul_pow, ← map_pow, ← map_pow, pow_right_comm] at this
    rw [← Units.val_pow_eq_pow_val, h', Units.val_mul, map_mul (algebraMap _ _), hδ, map_pow,
      ← mul_assoc, mul_right_comm, ← mul_pow] at this
    have := toto₂ (L := L) (n := p) (hS := this) (x := ((algebraMap (𝓞 F) F α ^ 2) * δ)⁻¹) _ sorry sorry
    rwa [inv_pow, mul_comm, map_pow, inv_mul_cancel_left₀] at this
    simp [hα, hδ₀]
  let ξ := rootOfSplitsXPowSubC hp.out.pos (ζ.val : F) L
  have hξ := rootOfSplitsXPowSubC_pow (ζ.val : F) L (n := p)
  have hξ' : IsPrimitiveRoot ξ (p ^ 2) := by
    refine IsPrimitiveRoot.iff_orderOf.mpr ?_
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, hξ, ← IsScalarTower.algebraMap_apply, FaithfulSMul.algebraMap_eq_one_iff]
      exact hζ.ne_one hp.out.one_lt
    · rw [one_add_one_eq_two, pow_two, pow_mul, hξ, ← map_pow, ← map_pow,
        ← IsScalarTower.algebraMap_apply, FaithfulSMul.algebraMap_eq_one_iff]
      exact hζ.pow_eq_one
  have : IsCyclotomicExtension {p ^ 2} ℚ ℚ⟮ξ⟯ := hξ'.intermediateField_adjoin_isCyclotomicExtension ℚ
  suffices IsCyclotomicExtension {p ^ 2} ℚ (⊤ : IntermediateField ℚ L) from
    IsCyclotomicExtension.equiv _ ℚ (⊤ : IntermediateField ℚ L) topEquiv
  have := (isCyclotomicExtension_singleton_iff_eq_adjoin (p ^ 2) ℚ _ ⊤ hξ').mpr
  apply this
  rw [eq_comm, eq_of_le_iff_finrank_eq le_top]
  rw [finrank_top', ← finrank_mul_finrank ℚ F L, finrank p F, Nat.totient_prime hp.out, hrF,
    IsCyclotomicExtension.Rat.finrank (p ^ 2) ℚ⟮ξ⟯, Nat.totient_prime_pow hp.out Nat.two_pos,
    Nat.add_one_sub_one, pow_one, mul_comm]

/-- Every cyclic extension of `ℚ` of prime degree `p` (odd) unramified outside `p` is contained
in the unique subfield of degree `p` of `ℚ(ζ_{p²})`. -/
theorem prop_kw_exponent_p
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
    (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p) :
    Nonempty (K →ₐ[ℚ] CyclotomicField (p ^ 2) ℚ) := by
  sorry

end

end
