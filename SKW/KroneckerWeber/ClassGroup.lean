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
public import SKW.PRed2Mathlib.Action
public import SKW.Prereqs.FractionalIdeal
public import SKW.Prereqs.CMField
public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.NumberField
public import SKW.Prereqs.Unramified

@[expose] public section

/-!
# Class group argument for Kronecker-Weber

Uses Stickelberger's theorem to show that if `(μ) = 𝔞ᵖ` in `𝓞_F`, then `𝔞` is principal,
hence `μ = αᵖ · η` for a unit `η ∈ 𝓞_F×`. A further unit argument shows `η` is a `p`-th power
times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`.
-/

open NumberField Ideal Polynomial Module IsCyclotomicExtension Rat

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

include hrF hIrr hμ in
/-- The product of `η` with its complex conjugate `σ₋₁(η)` is a `p`-th power in `F`: a consequence
of the Kummer relation `σ₋₁(μ) = ξᵖ · μ⁻¹` together with `μ = αᵖ · η`. -/
lemma kw_conj_mul_eq_pow {α : 𝓞 F} {η : (𝓞 F)ˣ} (h : μ = α ^ p * η) :
    ∃ w : F, (η : F) * (galEquivZMod p F).symm (-1) (η : F) = w ^ p := by
  obtain ⟨ξ, hξ₀, hξ⟩ : ∃ ξ, ξ ≠ 0 ∧
      (galEquivZMod p F).symm (-1) (μ : F) = ξ ^ p * (μ : F) ^ (-1 : ℤ) := by
    obtain ⟨ξ', hξ'₀, hξ'⟩ := kw_abelian_kummer p F hrF hIrr ((galEquivZMod p F).symm (-1))
    refine ⟨ξ' * μ, mul_ne_zero hξ'₀ (by simpa), ?_⟩
    rw [hξ', mul_pow, ← zpow_natCast (μ : F), ← zpow_natCast (μ : F), mul_assoc, ← zpow_add₀ (by simpa),
      MulEquiv.apply_symm_apply, show (p : ℤ) + -1 = (p - 1 : ℕ) by
        rw [Int.add_neg_one, Nat.cast_sub hp.out.one_le, Nat.cast_one],
      Units.coe_neg_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have hα0 : (α : F) ≠ 0 := by
    have : α ≠ 0 := by rintro rfl; rw [zero_pow hp.out.ne_zero, zero_mul] at h; exact hμ h
    exact_mod_cast this
  have hcα0 : (galEquivZMod p F).symm (-1) (α : F) ≠ 0 := by simp [hα0]
  have hμF : (μ : F) = (α : F) ^ p * (η : F) := by exact_mod_cast h
  rw [hμF, map_mul, map_pow, zpow_neg_one] at hξ
  field_simp [hα0, (by simp : (η : F) ≠ 0)] at hξ
  refine ⟨ξ * ((α : F) * (galEquivZMod p F).symm (-1) (α : F))⁻¹, ?_⟩
  rw [mul_pow, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero p (mul_ne_zero hα0 hcα0))]
  linear_combination hξ

include hrF hIrr hμ in
/-- In the Kummer setting `μ = αᵖ · η` with `(μ) = 𝔞ᵖ`, the fourth power `η⁴` factors as `ζ · δᵖ`
with `ζ` a `p`-th root of unity and `δ ∈ F` (a root of unity times a `p`-th power). -/
lemma kw_exists_realUnit_torsion [IsCMField F] (hp' : Odd p) {α : 𝓞 F} {η : (𝓞 F)ˣ}
    (h : μ = α ^ p * η) :
    ∃ (ζ : Units.torsion F) (δ : F), ζ.val.val ^ p = 1 ∧ δ ≠ 0 ∧ (η : F) ^ 4 = (ζ.val : F) * δ ^ p := by
  obtain ⟨ζ, ε, hε, h', hζ⟩ :
      ∃ (ζ : Units.torsion F) (ε : (𝓞 F)ˣ),
        ε ∈ IsCMField.realUnits F ∧ η ^ 4 = ζ * ε ∧ ζ.val.val ^ p = 1 := by
    obtain ⟨ζ, ε, hε, h'⟩ := IsCMField.exists_torsion_realunits_pow_two_eq_mul η
    have h₁ : Units.torsionOrder F = 2 * p := by
      rw [torsionOrder_eq (n := p), if_neg (Nat.not_even_iff_odd.mpr hp')]
    refine ⟨ζ ^ 2, ε ^ 2, pow_mem hε 2, ?_, ?_⟩
    · rw [SubmonoidClass.coe_pow, ← mul_pow, ← h', ← pow_mul]
    · rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← pow_mul, ← h₁, Units.torsionOrder,
        pow_card_eq_one, OneMemClass.coe_one, Units.val_one]
  have hη4 : (η : F) ^ 4 = (ζ.val : F) * (ε : F) := by exact_mod_cast congrArg Units.val h'
  have hζ' : ((galEquivZMod p F).symm (-1)) (ζ.val : F) = (ζ.val : F) ^ (-1 : ℤ) :=
    galEquivZMod_symm_apply_of_pow_eq p F (by simp) (by rw [← map_pow, hζ, map_one])
  obtain ⟨δ, -, hδ⟩ : ∃ δ : F, δ ≠ 0 ∧ (ε : F) = δ ^ p := by
    have hε' : (galEquivZMod p F).symm (-1) (ε : F) = (ε : F) := by
      rwa [galEquivZMod_symm_neg_one_apply p F, ← IsCMField.coe_ringOfIntegersComplexConj,
        algebraMap.coe_inj, ← IsCMField.coe_unitsComplexConj, ← Units.ext_iff,
        IsCMField.unitsComplexConj_eq_self_iff]
    obtain ⟨w, hw⟩ := kw_conj_mul_eq_pow p F hrF hμ hIrr h
    have hcη4 : (galEquivZMod p F).symm (-1) (η : F) ^ 4 = (ζ.val : F)⁻¹ * (ε : F) := by
      rw [← map_pow, hη4, map_mul, hζ', zpow_neg_one, hε']
    have key : (ε : F) ^ 2 = (w ^ 4) ^ p := by
      rw [(show (ε : F) ^ 2 = ((η : F) * (galEquivZMod p F).symm (-1) (η : F)) ^ 4 by
        rw [mul_pow, hη4, hcη4]; field_simp), hw, pow_right_comm]
    exact exists_eq_pow_of_pow_eq_pow_of_coprime (Nat.coprime_two_left.mpr hp') (by simp) key
  exact ⟨ζ, δ, hζ, fun hδ₀ ↦ by simp [hδ₀, zero_pow hp.out.ne_zero] at hδ, by rw [hη4, hδ]⟩

open IntermediateField Polynomial in
include hrF hIrr hμ in
/-- The unit `η` is a `p`-th power times a root of unity, so `L = F(ᵖ√μ) = ℚ(ζ_{p²})`. -/
lemma kw_unit_root_of_unity (hp' : Odd p) (K : IntermediateField ℚ L) [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p)
    (hL : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))) (h𝔞₀ : 𝔞 ≠ ⊥) (h𝔞 : 𝔞 ^ p = span {μ}) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  have : IsCMField F :=
    IsCyclotomicExtension.Rat.isCMField F (S := {p}) <|
      exists_eq_left.mpr <| (Nat.Prime.odd_iff hp.out).mp hp'
  have hF : (primitiveRoots p F).Nonempty := IsCyclotomicExtension.primitiveRoots_nonempty p ℚ F
  obtain ⟨α, η, hα, h⟩ := kw_mu_unit p F hμ h𝔞₀ h𝔞 (kw_class_trivial p F hrF hIrr h𝔞₀ h𝔞)
  obtain ⟨ζ, δ, hζ, hδ₀, hηδ⟩ := kw_exists_realUnit_torsion p F hrF hμ hIrr hp' h
  have h₁ : IsSplittingField F L (X ^ p - C (μ ^ 4 : F)) :=
    isSplittingField_X_pow_sub_C_pow_of_coprime _ hF hIrr <| hp'.coprime_two_left.pow_left 2
  have h₂ : Irreducible (X ^ p - C (μ ^ 4 : F)) := by
    rw [X_pow_sub_C_irreducible_iff_of_prime hp.out] at hIrr ⊢
    intro x hx
    obtain ⟨u, v, huv⟩ := (hp'.coprime_two_left.pow_left 2).isCoprime
    refine hIrr (x ^ u * μ ^ v) ?_
    rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm u, zpow_mul,
      zpow_natCast, hx, ← zpow_natCast, ← zpow_mul, mul_comm _ u, ← zpow_add₀ (by simpa), huv, zpow_one]
  have h₃ : IsSplittingField F L (X ^ p - C (ζ.val : F)) := by
    rw [h, RingOfIntegers.coe_eq_algebraMap, map_mul, mul_pow, hηδ, map_pow, pow_right_comm,
      ← mul_assoc, mul_right_comm, ← mul_pow, mul_comm] at h₁ h₂
    exact isSplittingField_X_pow_sub_C_of_mul_pow _ (by simpa [hα]) hF h₂
  have hζ : IsPrimitiveRoot ζ.val.val p := by
    refine IsPrimitiveRoot.iff_orderOf.mpr <| orderOf_eq_prime hζ fun h ↦ ?_
    rw [h, map_one] at h₃
    have := h₃.splits_iff.mp <| X_pow_sub_one_splits <| zeta_spec p ℚ F
    rw [eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one, hrF] at this
    exact hp.out.ne_one this
  let ξ := rootOfSplitsXPowSubC hp.out.pos (ζ.val : F) L
  have hξ := rootOfSplitsXPowSubC_pow (ζ.val : F) L (n := p)
  have hξ' : IsPrimitiveRoot ξ (p ^ 2) := by
    rw [pow_two]
    exact (hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) L)).of_pow_eq hξ hp.out.ne_zero
      (by aesop)
  have : IsCyclotomicExtension {p ^ 2} ℚ ℚ⟮ξ⟯ := hξ'.intermediateField_adjoin_isCyclotomicExtension ℚ
  suffices IsCyclotomicExtension {p ^ 2} ℚ (⊤ : IntermediateField ℚ L) from
    IsCyclotomicExtension.equiv _ ℚ (⊤ : IntermediateField ℚ L) topEquiv
  have := (isCyclotomicExtension_singleton_iff_eq_adjoin (p ^ 2) ℚ _ ⊤ hξ').mpr
  apply this
  rw [eq_comm, eq_of_le_iff_finrank_eq le_top]
  rw [finrank_top', ← finrank_mul_finrank ℚ F L, finrank p F, Nat.totient_prime hp.out, hrF,
    IsCyclotomicExtension.Rat.finrank (p ^ 2) ℚ⟮ξ⟯, Nat.totient_prime_pow hp.out Nat.two_pos,
    Nat.add_one_sub_one, pow_one, mul_comm]

end

/-! ### Tower (`IsScalarTower ℚ F L`) forms -/

noncomputable section IsScalarTower

variable (p : ℕ) [hp : Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]
variable {L : Type*} [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
  [IsGalois F L] [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p) [IsAbelianGalois ℚ L]
variable {𝔞 : Ideal (𝓞 F)} {μ : 𝓞 F} (hμ : μ ≠ 0)
  [hS : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))]
  (hIrr : Irreducible (X ^ p - C ((algebraMap (𝓞 F) F) μ)))

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
include hμ in
/-- Tower form of `kw_mu_unit`. -/
lemma kw_mu_unit'₁ (h𝔞₀ : 𝔞 ≠ ⊥) (h𝔞 : 𝔞 ^ p = span {μ}) (hcl : 𝔞.IsPrincipal) :
    ∃ (α : 𝓞 F) (η : (𝓞 F)ˣ), α ≠ 0 ∧ μ = α ^ p * η := by
  obtain ⟨α, rfl⟩ := hcl
  rw [span_singleton_pow, span_singleton_eq_span_singleton] at h𝔞
  obtain ⟨η, hη⟩ := h𝔞
  refine ⟨α, η, ?_, hη.symm⟩
  contrapose! hμ
  rw [← hη, hμ, zero_pow hp.out.ne_zero, zero_mul]

include hrF hIrr in
open Pointwise nonZeroDivisors FractionalIdeal in
/-- Tower form of `kw_class_trivial`. -/
lemma kw_class_trivial'₁ (h𝔞₀ : 𝔞 ≠ ⊥) (h𝔞 : 𝔞 ^ p = span {μ}) : 𝔞.IsPrincipal := by
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {p} ℚ F
  let 𝔞₀ : (Ideal (𝓞 F))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞₀⟩
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero h𝔞₀)]
  change ClassGroup.mk0 𝔞₀ = 1
  have h₁ {a : (ZMod p)ˣ} : ClassGroup.mk0 ((galEquivZMod p F).symm a • 𝔞₀) =
      ClassGroup.mk0 (𝔞₀ ^ a.val.val) := by
    rw [eq_comm, ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring F]
    obtain ⟨ξ, hξ₀, hξ⟩ := kw_abelian_kummer'₁ p F hrF hIrr ((galEquivZMod p F).symm a)
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

include hrF hIrr hμ in
/-- Tower form of `kw_conj_mul_eq_pow`. -/
lemma kw_conj_mul_eq_pow'₁ {α : 𝓞 F} {η : (𝓞 F)ˣ} (h : μ = α ^ p * η) :
    ∃ w : F, (η : F) * (galEquivZMod p F).symm (-1) (η : F) = w ^ p := by
  obtain ⟨ξ, hξ₀, hξ⟩ : ∃ ξ, ξ ≠ 0 ∧
      (galEquivZMod p F).symm (-1) (μ : F) = ξ ^ p * (μ : F) ^ (-1 : ℤ) := by
    obtain ⟨ξ', hξ'₀, hξ'⟩ := kw_abelian_kummer'₁ p F hrF hIrr ((galEquivZMod p F).symm (-1))
    refine ⟨ξ' * μ, mul_ne_zero hξ'₀ (by simpa), ?_⟩
    rw [hξ', mul_pow, ← zpow_natCast (μ : F), ← zpow_natCast (μ : F), mul_assoc, ← zpow_add₀ (by simpa),
      MulEquiv.apply_symm_apply, show (p : ℤ) + -1 = (p - 1 : ℕ) by
        rw [Int.add_neg_one, Nat.cast_sub hp.out.one_le, Nat.cast_one],
      Units.coe_neg_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  have hα0 : (α : F) ≠ 0 := by
    have : α ≠ 0 := by rintro rfl; rw [zero_pow hp.out.ne_zero, zero_mul] at h; exact hμ h
    exact_mod_cast this
  have hcα0 : (galEquivZMod p F).symm (-1) (α : F) ≠ 0 := by simp [hα0]
  have hμF : (μ : F) = (α : F) ^ p * (η : F) := by exact_mod_cast h
  rw [hμF, map_mul, map_pow, zpow_neg_one] at hξ
  field_simp [hα0, (by simp : (η : F) ≠ 0)] at hξ
  refine ⟨ξ * ((α : F) * (galEquivZMod p F).symm (-1) (α : F))⁻¹, ?_⟩
  rw [mul_pow, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero p (mul_ne_zero hα0 hcα0))]
  linear_combination hξ

include hrF hIrr hμ in
/-- Tower form of `kw_exists_realUnit_torsion`. -/
lemma kw_exists_realUnit_torsion'₁ [IsCMField F] (hp' : Odd p) {α : 𝓞 F} {η : (𝓞 F)ˣ}
    (h : μ = α ^ p * η) :
    ∃ (ζ : Units.torsion F) (δ : F), ζ.val.val ^ p = 1 ∧ δ ≠ 0 ∧ (η : F) ^ 4 = (ζ.val : F) * δ ^ p := by
  obtain ⟨ζ, ε, hε, h', hζ⟩ :
      ∃ (ζ : Units.torsion F) (ε : (𝓞 F)ˣ),
        ε ∈ IsCMField.realUnits F ∧ η ^ 4 = ζ * ε ∧ ζ.val.val ^ p = 1 := by
    obtain ⟨ζ, ε, hε, h'⟩ := IsCMField.exists_torsion_realunits_pow_two_eq_mul η
    have h₁ : Units.torsionOrder F = 2 * p := by
      rw [torsionOrder_eq (n := p), if_neg (Nat.not_even_iff_odd.mpr hp')]
    refine ⟨ζ ^ 2, ε ^ 2, pow_mem hε 2, ?_, ?_⟩
    · rw [SubmonoidClass.coe_pow, ← mul_pow, ← h', ← pow_mul]
    · rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← pow_mul, ← h₁, Units.torsionOrder,
        pow_card_eq_one, OneMemClass.coe_one, Units.val_one]
  have hη4 : (η : F) ^ 4 = (ζ.val : F) * (ε : F) := by exact_mod_cast congrArg Units.val h'
  have hζ' : ((galEquivZMod p F).symm (-1)) (ζ.val : F) = (ζ.val : F) ^ (-1 : ℤ) :=
    galEquivZMod_symm_apply_of_pow_eq p F (by simp) (by rw [← map_pow, hζ, map_one])
  obtain ⟨δ, -, hδ⟩ : ∃ δ : F, δ ≠ 0 ∧ (ε : F) = δ ^ p := by
    have hε' : (galEquivZMod p F).symm (-1) (ε : F) = (ε : F) := by
      rwa [galEquivZMod_symm_neg_one_apply p F, ← IsCMField.coe_ringOfIntegersComplexConj,
        algebraMap.coe_inj, ← IsCMField.coe_unitsComplexConj, ← Units.ext_iff,
        IsCMField.unitsComplexConj_eq_self_iff]
    obtain ⟨w, hw⟩ := kw_conj_mul_eq_pow'₁ p F hrF hμ hIrr h
    have hcη4 : (galEquivZMod p F).symm (-1) (η : F) ^ 4 = (ζ.val : F)⁻¹ * (ε : F) := by
      rw [← map_pow, hη4, map_mul, hζ', zpow_neg_one, hε']
    have key : (ε : F) ^ 2 = (w ^ 4) ^ p := by
      rw [(show (ε : F) ^ 2 = ((η : F) * (galEquivZMod p F).symm (-1) (η : F)) ^ 4 by
        rw [mul_pow, hη4, hcη4]; field_simp), hw, pow_right_comm]
    exact exists_eq_pow_of_pow_eq_pow_of_coprime (Nat.coprime_two_left.mpr hp') (by simp) key
  exact ⟨ζ, δ, hζ, fun hδ₀ ↦ by simp [hδ₀, zero_pow hp.out.ne_zero] at hδ, by rw [hη4, hδ]⟩

open IntermediateField Polynomial in
include hrF hIrr hμ in
/-- Tower form of `kw_unit_root_of_unity`: the vestigial `K`/`hL` hypotheses are dropped. -/
lemma kw_unit_root_of_unity'₁ (hp' : Odd p) (h𝔞₀ : 𝔞 ≠ ⊥) (h𝔞 : 𝔞 ^ p = span {μ}) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  have : IsCMField F :=
    IsCyclotomicExtension.Rat.isCMField F (S := {p}) <|
      exists_eq_left.mpr <| (Nat.Prime.odd_iff hp.out).mp hp'
  have hF : (primitiveRoots p F).Nonempty := IsCyclotomicExtension.primitiveRoots_nonempty p ℚ F
  obtain ⟨α, η, hα, h⟩ := kw_mu_unit'₁ p F hμ h𝔞₀ h𝔞 (kw_class_trivial'₁ p F hrF hIrr h𝔞₀ h𝔞)
  obtain ⟨ζ, δ, hζ, hδ₀, hηδ⟩ := kw_exists_realUnit_torsion'₁ p F hrF hμ hIrr hp' h
  have h₁ : IsSplittingField F L (X ^ p - C (μ ^ 4 : F)) :=
    isSplittingField_X_pow_sub_C_pow_of_coprime _ hF hIrr <| hp'.coprime_two_left.pow_left 2
  have h₂ : Irreducible (X ^ p - C (μ ^ 4 : F)) := by
    rw [X_pow_sub_C_irreducible_iff_of_prime hp.out] at hIrr ⊢
    intro x hx
    obtain ⟨u, v, huv⟩ := (hp'.coprime_two_left.pow_left 2).isCoprime
    refine hIrr (x ^ u * μ ^ v) ?_
    rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm u, zpow_mul,
      zpow_natCast, hx, ← zpow_natCast, ← zpow_mul, mul_comm _ u, ← zpow_add₀ (by simpa), huv, zpow_one]
  have h₃ : IsSplittingField F L (X ^ p - C (ζ.val : F)) := by
    rw [h, RingOfIntegers.coe_eq_algebraMap, map_mul, mul_pow, hηδ, map_pow, pow_right_comm,
      ← mul_assoc, mul_right_comm, ← mul_pow, mul_comm] at h₁ h₂
    exact isSplittingField_X_pow_sub_C_of_mul_pow _ (by simpa [hα]) hF h₂
  have hζ : IsPrimitiveRoot ζ.val.val p := by
    refine IsPrimitiveRoot.iff_orderOf.mpr <| orderOf_eq_prime hζ fun h ↦ ?_
    rw [h, map_one] at h₃
    have := h₃.splits_iff.mp <| X_pow_sub_one_splits <| zeta_spec p ℚ F
    rw [eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one, hrF] at this
    exact hp.out.ne_one this
  let ξ := rootOfSplitsXPowSubC hp.out.pos (ζ.val : F) L
  have hξ := rootOfSplitsXPowSubC_pow (ζ.val : F) L (n := p)
  have hξ' : IsPrimitiveRoot ξ (p ^ 2) := by
    rw [pow_two]
    exact (hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) L)).of_pow_eq hξ hp.out.ne_zero
      (by aesop)
  have : IsCyclotomicExtension {p ^ 2} ℚ ℚ⟮ξ⟯ := hξ'.intermediateField_adjoin_isCyclotomicExtension ℚ
  suffices IsCyclotomicExtension {p ^ 2} ℚ (⊤ : IntermediateField ℚ L) from
    IsCyclotomicExtension.equiv _ ℚ (⊤ : IntermediateField ℚ L) topEquiv
  have := (isCyclotomicExtension_singleton_iff_eq_adjoin (p ^ 2) ℚ _ ⊤ hξ').mpr
  apply this
  rw [eq_comm, eq_of_le_iff_finrank_eq le_top]
  rw [finrank_top', ← finrank_mul_finrank ℚ F L, finrank p F, Nat.totient_prime hp.out, hrF,
    IsCyclotomicExtension.Rat.finrank (p ^ 2) ℚ⟮ξ⟯, Nat.totient_prime_pow hp.out Nat.two_pos,
    Nat.add_one_sub_one, pow_one, mul_comm]

end IsScalarTower

end
