module

public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.IntermediateFields
public import SKW.Prereqs.NumberTheory
public import SKW.Prereqs.CMField

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

theorem IsPrimitiveRoot.isIntegral' {n : ℕ} {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    {μ : L} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) :
    IsIntegral K μ :=
  IsIntegral.tower_top (h.isIntegral hpos)

/-- Companion to `orderOf_pow'`: if every prime factor of `m` divides `orderOf (y ^ m)`, then
`orderOf y = m * orderOf (y ^ m)`. -/
theorem orderOf_eq_mul_orderOf_pow {M : Type*} [Monoid M] {y : M} {m : ℕ} (hm : m ≠ 0)
    (h : ∀ q, q.Prime → q ∣ m → q ∣ orderOf (y ^ m)) : orderOf y = m * orderOf (y ^ m) := by
  have h₁ : m / Nat.gcd (orderOf y) m = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    refine fun q hq hqd ↦ hq.one_lt.ne' <| Nat.dvd_one.mp ?_
    refine (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hm.bot_lt)).symm ▸ Nat.dvd_gcd hqd ?_
    rw [← orderOf_pow' y hm]
    exact h q hq (hqd.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
  have h₂ : Nat.gcd (orderOf y) m = m := by
    conv_rhs => rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right (orderOf y) m), h₁, mul_one]
  rw [orderOf_pow' y hm, h₂, Nat.mul_div_cancel' (h₂ ▸ Nat.gcd_dvd_left (orderOf y) m)]

/-- An `m`-th root of a primitive `n`-th root of unity is a primitive `(m * n)`-th root of unity,
provided every prime factor of `m` divides `n`. -/
theorem IsPrimitiveRoot.of_pow_eq {M : Type*} [CommMonoid M] {ζ y : M} {m n : ℕ}
    (h : IsPrimitiveRoot ζ n) (hy : y ^ m = ζ) (hm : m ≠ 0)
    (hmn : ∀ q, q.Prime → q ∣ m → q ∣ n) : IsPrimitiveRoot y (m * n) := by
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_eq_mul_orderOf_pow hm
    (fun q hq hqm => by rw [hy, ← h.eq_orderOf]; exact hmn q hq hqm), hy, ← h.eq_orderOf]

/-! ### IsCyclotomicExtension -/

theorem IsCyclotomicExtension.primitiveRoots_nonempty (n : ℕ) [NeZero n] (A B : Type*) [CommRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [hC : IsCyclotomicExtension {n} A B] :
    (primitiveRoots n B).Nonempty :=
  ⟨hC.zeta, (mem_primitiveRoots (NeZero.pos n)).mpr hC.zeta_spec⟩

open NumberField in
theorem IsCyclotomicExtension.Rat.discr_coprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (K₁ K₂ : Type*)
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂] [IsCyclotomicExtension {n₁} ℚ K₁]
    [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
  rw [Int.isCoprime_iff_nat_coprime, natAbs_discr  n₁ K₁, natAbs_discr  n₂ K₂]
  refine Nat.Coprime.coprime_div_left ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
  refine Nat.Coprime.coprime_div_right ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
  exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ h)

theorem IntermediateField.linearDisjoint_iff'' {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : IntermediateField F E) (L : Type*) [Field L] [Algebra F L] [Algebra L E]
    [IsScalarTower F L E] :
    A.LinearDisjoint L ↔ A.LinearDisjoint (IsScalarTower.toAlgHom F L E).fieldRange := by
  rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]

theorem IsCyclotomicExtension.Rat.linearDisjoint_ofCoprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    {E : Type*} [Field E] [NumberField E] (K₁ : IntermediateField ℚ E) [NumberField K₁] (K₂ : Type*)
    [Field K₂] [NumberField K₂] [Algebra K₂ E] [IsCyclotomicExtension {n₁} ℚ K₁]
    [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    K₁.LinearDisjoint K₂ := by
  have : IsCyclotomicExtension {n₂} ℚ (IsScalarTower.toAlgHom ℚ K₂ E).fieldRange :=
    .equiv _ ℚ K₂ (IsScalarTower.toAlgHom ℚ K₂ E).equivFieldRange
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois {n₁} ℚ K₁
  rw [IntermediateField.linearDisjoint_iff'']
  exact NumberField.linearDisjoint_of_isGalois_isCoprime_discr E _ _ <| discr_coprime n₁ n₂ K₁ _ h

open IntermediateField

set_option backward.isDefEq.respectTransparency false in
theorem IsCyclotomicExtension.Rat.gcd_inf {K : Type*} [Field K] [NumberField K]
    (n₁ n₂ : ℕ) (F₁ F₂ : IntermediateField ℚ K) [h₁ : IsCyclotomicExtension {n₁} ℚ F₁]
    [h₂ : IsCyclotomicExtension {n₂} ℚ F₂] [NeZero n₁] [NeZero n₂] :
    IsCyclotomicExtension {n₁.gcd n₂} ℚ ↑(F₁ ⊓ F₂) := by
  let d := n₁.gcd n₂
  have : NeZero d := ⟨Nat.gcd_ne_zero_left (NeZero.ne _)⟩
  have : NeZero (n₁.lcm n₂) := ⟨Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨ζ₁, hζ₁⟩ := h₁.1 rfl (NeZero.ne n₁)
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective F₁ K)
  obtain ⟨s, hs⟩ := n₁.gcd_dvd_left n₂
  let ζ := (algebraMap F₁ K ζ₁) ^ s
  have hζ : IsPrimitiveRoot ζ d := hζ₁.pow (NeZero.pos n₁) (by rwa [mul_comm])
  have : IsCyclotomicExtension {d} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  rw [isCyclotomicExtension_singleton_iff_eq_adjoin d ℚ K _ hζ, eq_comm]
  rw [eq_of_le_iff_finrank_eq]
  · have : IsGalois ℚ F₁ := h₁.isGalois
    have := isCyclotomicExtension_lcm_sup ℚ K n₁ n₂ F₁ F₂
    have : Module.finrank ℚ ↑(F₁ ⊔ F₂) ≠ 0 := Module.finrank_pos.ne'
    rw [← mul_right_inj' this, finrank_sup_mul_finrank_inf_eq, IsCyclotomicExtension.Rat.finrank n₁ F₁,
      IsCyclotomicExtension.Rat.finrank n₂ F₂, IsCyclotomicExtension.Rat.finrank (n₁.lcm n₂) ↑(F₁ ⊔ F₂),
      IsCyclotomicExtension.Rat.finrank d ℚ⟮ζ⟯, ← Nat.totient_mul_totient_eq]
  · obtain ⟨ζ₂, hζ₂⟩ := h₂.1 rfl (NeZero.ne n₂)
    replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective F₂ K)
    rw [(isCyclotomicExtension_singleton_iff_eq_adjoin n₁ ℚ K _ hζ₁).mp h₁,
      (isCyclotomicExtension_singleton_iff_eq_adjoin n₂ ℚ K _ hζ₂).mp h₂, adjoin_simple_le_iff, mem_inf]
    constructor
    · exact pow_mem (mem_adjoin_simple_self ℚ _) s
    · obtain ⟨t, _, ht⟩ := hζ₂.eq_pow_of_pow_eq_one <| (hζ.pow_eq_one_iff_dvd n₂).mpr (n₁.gcd_dvd_right n₂)
      rw [← ht]
      exact pow_mem (mem_adjoin_simple_self ℚ _) t

open IsCyclotomicExtension.Rat NumberField

theorem IsCyclotomicExtension.Rat.ringHom_galEquivZMod_apply {E F :Type*} [Field E] [Field F]
    [NumberField E] [NumberField F] {n : ℕ} [NeZero n] [hE : IsCyclotomicExtension {n} ℚ E]
    [hF : IsCyclotomicExtension {n} ℚ F] (f : E →+* F) (a : (ZMod n)ˣ) (x : E) :
    f ((galEquivZMod n E).symm a x) = (galEquivZMod n F).symm a (f x) := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ E
  have hζp := IsCyclotomicExtension.zeta_pow n ℚ E
  suffices f.toRatAlgHom.comp ((galEquivZMod n E).symm a) =
    ((galEquivZMod n F).symm a).toAlgHom.comp f.toRatAlgHom from AlgHom.congr_fun this x
  refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) ?_
  simp only [Set.eqOn_singleton, AlgHom.coe_comp, AlgEquiv.coe_algHom, RingHom.toRatAlgHom_apply,
    Function.comp_apply]
  rw [galEquivZMod_apply_of_pow_eq n _ _ hζp,
    galEquivZMod_apply_of_pow_eq n _ _ (by rw [← map_pow, hζp, map_one]), map_pow,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

@[simp]
def IsFractionRing.map_apply_algebraMap {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L]
    {j : A →+* B} (hj : Function.Injective j) (x : A) :
    IsFractionRing.map hj (algebraMap A K x) = algebraMap B L (j x) := by simp [map]

theorem IsCyclotomicExtension.Rat.ringHom_galEquivZMod_smul {E F :Type*} [Field E] [Field F]
    [NumberField E] [NumberField F] {n : ℕ} [NeZero n]
    [hE : IsCyclotomicExtension {n} ℚ E] [hF : IsCyclotomicExtension {n} ℚ F]
    {f : 𝓞 E →+* 𝓞 F} (hf : Function.Injective f) (a : (ZMod n)ˣ) (x : 𝓞 E) :
    f ((galEquivZMod n E).symm a • x) = (galEquivZMod n F).symm a • (f x) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  rw [← IsFractionRing.map_apply_algebraMap (K := E) hf]
  have := ringHom_galEquivZMod_apply (F := F) (IsFractionRing.map hf) a (algebraMap (𝓞 E) E x)
  rwa [IsFractionRing.map_apply_algebraMap] at this

/-- The automorphism of `ℚ(ζ_n)` corresponding to `a ∈ (ℤ/nℤ)ˣ` under `galEquivZMod` acts on every
`n`-th root of unity as raising to the `z`-th power, for any integer `z` representing `a`. -/
theorem IsCyclotomicExtension.Rat.galEquivZMod_symm_apply_of_pow_eq {n : ℕ} [NeZero n]
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] {a : (ZMod n)ˣ} {z : ℤ}
    (haz : (z : ZMod n) = a) {x : F} (hx : x ^ n = 1) :
    (galEquivZMod n F).symm a x = x ^ z := by
  have hx₀ : x ≠ 0 := fun h ↦ by simp [h, zero_pow (NeZero.ne n)] at hx
  rw [galEquivZMod_apply_of_pow_eq n F _ hx, MulEquiv.apply_symm_apply]
  obtain ⟨k, hk⟩ : (n : ℤ) ∣ z - ((a : ZMod n).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      ZMod.natCast_zmod_val, haz, sub_self]
  rw [show z = ((a : ZMod n).val : ℤ) + n * k from by linarith, zpow_add₀ hx₀, zpow_mul,
    zpow_natCast, zpow_natCast, hx, one_zpow, mul_one]

open NumberField IsCMField in
/-- For an odd prime `n`, the automorphism of `ℚ(ζ_n)` corresponding to `-1 ∈ (ℤ/nℤ)ˣ` under
`galEquivZMod` is the complex conjugation of the CM-field `ℚ(ζ_n)`.

This bridges the ad-hoc conjugation `(galEquivZMod p F).symm (-1)` used in the Kummer argument to
the mathlib `complexConj` API: `ε ∈ realUnits F` is then fixed by it
(via `Units.complexConj_eq_self_iff`), and a `p`-th root of unity is sent to its inverse. -/
theorem IsCyclotomicExtension.Rat.galEquivZMod_symm_neg_one_apply {n : ℕ} [NeZero n]
    {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] [IsCMField F] (x : F) :
    (galEquivZMod n F).symm (-1) x = complexConj F x := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  let φ : F →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  suffices h : (galEquivZMod n F).symm (-1) = (complexConj F).restrictScalars ℚ by
    rw [← AlgEquiv.restrictScalars_apply ℚ (complexConj F), ← h]
  refine AlgEquiv.coe_algHom_injective <| AlgHom.ext_of_adjoin_eq_top
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) (Set.eqOn_singleton.mpr ?_)
  show (galEquivZMod n F).symm (-1) (zeta n ℚ F) = (complexConj F).restrictScalars ℚ (zeta n ℚ F)
  rw [galEquivZMod_symm_apply_of_pow_eq (z := -1) (by simp) (zeta_pow n ℚ F), zpow_neg_one,
    AlgEquiv.restrictScalars_apply, (isConj_complexConj F φ).eq_inv_of_isPrimitiveRoot hζ]
