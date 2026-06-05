module

public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.IntermediateFields
public import SKW.Prereqs.NumberTheory

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

@[expose] public section

theorem IsPrimitiveRoot.isIntegral' {n : ℕ} {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    {μ : L} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) :
    IsIntegral K μ :=
  IsIntegral.tower_top (h.isIntegral hpos)

/-! ### IsCyclotomicExtension -/

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
    .equiv _ ℚ K₂ (AlgHom.equivFieldRange _)
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
