module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

public import SKW.Chapter1.AddCharTrace
public import SKW.Chapter1.Teichmuller

@[expose] public section

noncomputable section

open Ideal NumberField IntermediateField

variable (p f : ℕ) [NeZero (p ^ f - 1)]

local notation3 "𝒑" => span {(p : ℤ)}

theorem three_le_p_pow [hp : Fact (p.Prime)] [hp' : Fact (Odd p)] : 3 ≤ p ^ f := by
  have hf : 0 < f := by
    by_contra!
    aesop
  refine le_trans (Nat.le_pow hf) ?_
  exact (Nat.pow_le_pow_iff_left hf.ne').mpr <| (Nat.Prime.odd_iff hp.out).mp hp'.out

theorem coprime_pow_sub_one [Fact (p.Prime)] : (p ^ f - 1).Coprime p := by
  have hf : f ≠ 0 := by
    by_contra!; aesop
  rw [← Nat.coprime_pow_right_iff hf.pos, Nat.coprime_self_sub_left NeZero.one_le]
  exact Nat.gcd_one_left _

variable {p f}

-- variable {L : Type*} [Field L] {ζ η : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)
--    (hη : IsPrimitiveRoot η (p ^ f - 1)) (𝓟 : Ideal (𝓞 L))

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
  {P : Ideal (𝓞 K)}

variable (hbij : Function.Bijective (rootsOfUnity.mapQuot (p ^ f - 1) P))

variable {L : Type*} [Field L] [Algebra K L] {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p) (𝓟 : Ideal (𝓞 L))

theorem teichmuller_pow_comp_algebraMap_ne_one (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    (teichmuller hbij ^ (- a)).ringHomComp (algebraMap (𝓞 K) (𝓞 L)) ≠ 1 := by
  have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
  rwa [← MulChar.ringHomComp_zpow, ne_eq, ← orderOf_dvd_iff_zpow_eq_one, ← MulChar.ringHomCompHom_apply,
    orderOf_injective (MulChar.ringHomCompHom (algebraMap (𝓞 K) (𝓞 L)))
    (MulChar.injective_ringHomComp (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))),
    orderOf_teichmuller hbij hη, Int.dvd_neg]

theorem teichmuller_ne_one [Fact (p.Prime)] [Fact (Odd p)] : teichmuller hbij ≠ 1 := by
  have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
  rw [ne_eq, ← orderOf_eq_one_iff, orderOf_teichmuller hbij hη, Nat.pred_eq_succ_iff, zero_add]
  exact ne_of_gt <| three_le_p_pow _ _

variable [P.IsMaximal]

local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

variable [NumberField L] [𝓟.IsPrime]

local notation3 "F" => ℚ⟮(ζ : L)⟯
local notation3 "ζ₀" => IntermediateField.AdjoinSimple.gen ℚ (ζ : L)

variable (p)

include hζ in
theorem isPrimitiveRoot_zeta₀ :
    IsPrimitiveRoot ζ₀ p := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ (FaithfulSMul.algebraMap_injective F L)
  rw [AdjoinSimple.algebraMap_gen]
  exact hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 L) L)

include hζ in
theorem F_isCyclotomicExtension [NeZero p] :
    IsCyclotomicExtension {p} ℚ F := by
  refine IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension ℚ ?_
  exact hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 L) L)

theorem algebraMap_zeta₀ [NeZero p] (hζ₀ : IsPrimitiveRoot ζ₀ p) :
    algebraMap (𝓞 F) (𝓞 L) hζ₀.toInteger = ζ := by
  apply FaithfulSMul.algebraMap_injective (𝓞 L) L
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F L,
    RingOfIntegers.map_mk, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen]

variable {p} [hp : Fact (p.Prime)]

include hζ in
theorem zeta_sub_one_mem [𝓟.LiesOver 𝒑] : ζ - 1 ∈ 𝓟 := by
  have := F_isCyclotomicExtension p hζ
  have hζ₀ := isPrimitiveRoot_zeta₀ p hζ
  rw [← algebraMap_zeta₀ p hζ₀, ← map_one (f := algebraMap (𝓞 F) (𝓞 L)), ← map_sub, ← mem_comap,
    ← Ideal.under_def, IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p F hζ₀ (under (𝓞 F) 𝓟)]
  exact Submodule.mem_span_singleton_self _

variable (p f P) in
theorem ramificationIdx_eq_p_sub_one [𝓟.LiesOver P] [P.LiesOver 𝒑]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    P.ramificationIdx 𝓟 = p - 1 := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have h : ¬p ∣ p ^ f - 1 := by
    rw [Nat.dvd_sub_iff_right NeZero.one_le (p.div_pow_of_pos f _), Nat.dvd_one]
    · exact hp.out.ne_one
    · by_contra! h
      aesop
  have := Ideal.ramificationIdx_algebra_tower' 𝒑 P 𝓟
  rwa [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P h,
    IsCyclotomicExtension.Rat.ramificationIdx_eq  (p * (p ^ f - 1)) L 𝓟 _ h, pow_zero, one_mul,
    one_mul, eq_comm] at this
  rw [zero_add, pow_one]

def GaussSum [P.LiesOver 𝒑] (a : ℤ) : 𝓞 L :=
  gaussSum ((teichmuller hbij ^ (- a)).ringHomComp (algebraMap (𝓞 K) (𝓞 L))) (addCharTrace P hζ)

theorem GaussSum_mem [𝓟.LiesOver 𝒑] [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    GaussSum hbij hζ a ∈ 𝓟 := by
  have h𝓟 := zeta_sub_one_mem hζ 𝓟
  have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
  simp_rw [← Quotient.eq_zero_iff_mem, GaussSum, gaussSum, map_sum, map_mul,
    addCharTrace_mk_eq_one _ _ h𝓟, mul_one, ← map_sum]
  rw [MulChar.sum_eq_zero_of_ne_one (teichmuller_pow_comp_algebraMap_ne_one hbij a ha), map_zero]

theorem norm_GaussSum [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    ∃ k : ℕ, 1 ≤ k ∧ (Algebra.norm ℤ (GaussSum hbij hζ a)).natAbs = p ^ k := by
  have := congr_arg (fun x ↦ Int.natAbs (Algebra.norm ℤ x)) <|
    gaussSum_mul_gaussSum_eq_card (teichmuller_pow_comp_algebraMap_ne_one hbij a ha)
      (addCharTrace_isPrimitive P hζ)
  dsimp at this
  rw [map_mul, Fintype.card_eq_nat_card, ← absNorm_eq_card, absNorm_eq_pow_inertiaDeg' P hp.out,
    Nat.cast_pow, map_pow,  show (p : 𝓞 L) = algebraMap ℤ (𝓞 L) p by simp,
    Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis L), ← pow_mul,
    Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (Dvd.intro _ this)
  refine ⟨k, ?_, by rwa [GaussSum]⟩
  obtain ⟨Q, hQ, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝒑
  by_contra!
  refine Ideal.IsMaximal.ne_top hQ ?_
  refine Ideal.eq_top_of_isUnit_mem _ (GaussSum_mem hbij hζ Q a ha) ?_
  rw [GaussSum, isUnit_iff_norm', hk, Nat.lt_one_iff.mp this, pow_zero]

theorem GaussSum_ne_zero [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    GaussSum hbij hζ a ≠ 0 := by
  rw [← Algebra.norm_ne_zero_iff (R := ℤ), ← Int.natAbs_ne_zero]
  obtain ⟨k, hk, hk'⟩ := norm_GaussSum hbij hζ a ha
  have := hp.out
  aesop

theorem sum_sum_inv_mul_pow_eq_neg_one [P.LiesOver 𝒑] :
    ∑ x : 𝓞 K ⧸ P,
      ∑ i ∈ Finset.range (Module.finrank (ℤ ⧸ 𝒑) (𝓞 K ⧸ P)), x⁻¹ * x ^ Nat.card (ℤ ⧸ 𝒑) ^ i = - 1 := by
  classical
  have := hp.out.one_lt
  rw [Finset.sum_comm]
  have (i : ℕ) :  ∑ x : 𝓞 K ⧸ P, x⁻¹ * x ^ Nat.card (ℤ ⧸ 𝒑) ^ i =
      ∑ x : (𝓞 K ⧸ P)ˣ, (x : 𝓞 K ⧸ P) ^ (Nat.card (ℤ ⧸ 𝒑) ^ i - 1) := by
    rw [← Finset.sum_sdiff ({0} : Finset _).subset_univ, Finset.sum_singleton, inv_zero, zero_mul,
      add_zero, Finset.sum_subtype (p := fun x ↦ x ≠ 0) («F» := inferInstance) _ (by simp)]
    refine Finset.sum_equiv unitsEquivNeZero.symm (by simp) fun ⟨x, hx⟩ _ ↦ ?_
    simp only [ne_eq, unitsEquivNeZero_symm_apply, Units.val_mk0]
    rw [mul_comm, ← zpow_natCast, ← zpow_sub_one₀ hx, ← Nat.cast_pred, zpow_natCast]
    refine Nat.pow_pos Nat.card_pos
  simp_rw [this, FiniteField.sum_pow_units]
  rw [← Nat.succ_pred_eq_of_pos Module.finrank_pos, ← Ideal.inertiaDeg_algebraMap, Finset.sum_range_succ',
    pow_zero, Nat.sub_self, if_pos (Nat.dvd_zero _), Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [if_neg]
  rw [Fintype.card_eq_nat_card, ← Ideal.absNorm_eq_card, Int.card_ideal_quot,
    Ideal.absNorm_eq_pow_inertiaDeg' P hp.out]
  apply Nat.not_dvd_of_pos_of_lt (by aesop)
  gcongr
  · exact NeZero.one_le
  · rwa [Nat.pred_eq_sub_one, Finset.mem_range, ← Nat.add_lt_iff_lt_sub_right] at hi

variable [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]

theorem mk_sq_gausssum_eq [hp' : Fact (Odd p)] [𝓟.LiesOver P] [P.LiesOver 𝒑] :
    Ideal.Quotient.mk (𝓟 ^ 2) (GaussSum hbij hζ 1) = -(ζ - 1 : 𝓞 L) := by
  have : 3 ≤ p := (Nat.Prime.odd_iff hp.out).mp hp'.out
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have : (𝓟 ^ 2).LiesOver P := by
    refine pow_liesOver_of_liesOver P 𝓟 ?_
    rw [ramificationIdx_eq_p_sub_one p f]
    grind
  have : (𝓟 ^ 2).LiesOver 𝒑 := LiesOver.trans (𝓟 ^ 2) P 𝒑
  have h𝓟 := zeta_sub_one_mem hζ 𝓟
  have h : (teichmuller hbij)⁻¹ ≠ 1 := by
    have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
    refine inv_ne_one.mpr ?_
    exact teichmuller_ne_one hbij
  simp_rw [GaussSum, gaussSum, zpow_neg, zpow_one, MulChar.ringHomComp_apply, map_sum, map_mul,
      addCharTrace_mk_sq_eq P hζ h𝓟, mul_add, mul_one, Finset.sum_add_distrib, ← map_sum,
      MulChar.sum_eq_zero_of_ne_one h, map_zero, zero_add, Algebra.smul_def, ← mul_assoc,
      ← Finset.sum_mul, Ideal.Quotient.mk_algebraMap,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2), Quotient.algebraMap_eq,
      MulChar.inv_apply', teichmuller_mk_eq,
      IsScalarTower.algebraMap_apply (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2),
      FiniteField.algebraMap_trace_eq_sum_pow, map_sum, Finset.mul_sum, ← map_mul, ← map_sum]
  rw [sum_sum_inv_mul_pow_eq_neg_one, map_neg, map_one, neg_one_mul, map_neg]

set_option backward.isDefEq.respectTransparency false in
variable (p f K) in
def galFEquiv : Gal(L/F) ≃* (ZMod (p ^ f - 1))ˣ :=
  letI K' := (IsScalarTower.toAlgHom ℚ K L).fieldRange
  haveI := F_isCyclotomicExtension p hζ
  haveI := IsCyclotomicExtension.isAbelianGalois {p * (p ^ f - 1)} ℚ L
  haveI : IsCyclotomicExtension {p ^ f - 1} ℚ K' := .equiv _ ℚ K
    (IsScalarTower.toAlgHom ℚ K L).equivFieldRange
  haveI := IsCyclotomicExtension.isAbelianGalois {p ^ f - 1} ℚ K'
  (MulEquiv.ofBijective (IntermediateField.restrictRestrictAlgEquivMapHom ℚ K' F L)
    ⟨by
      refine IntermediateField.restrictRestrictAlgEquivMapHom_injective _ _ ?_
      have : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ (⊤ : IntermediateField ℚ L) :=
      IsCyclotomicExtension.equiv _ _ _ topEquiv.symm
      have : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ ↥(K' ⊔ F) := by
        rw [mul_comm, ← Nat.Coprime.lcm_eq_mul (coprime_pow_sub_one p f)]
        exact isCyclotomicExtension_lcm_sup ℚ L (p ^ f - 1) p  K' F
      exact isCyclotomicExtension_eq {p * (p ^ f - 1)}  ℚ L _ _,
    by
      refine IntermediateField.restrictRestrictAlgEquivMapHom_surjective K' F ?_
      apply IntermediateField.LinearDisjoint.inf_eq_bot
      apply IsCyclotomicExtension.Rat.linearDisjoint_ofCoprime (p ^ f - 1) p K' F
        (coprime_pow_sub_one p f)⟩).trans<| IsCyclotomicExtension.Rat.galEquivZMod (p ^ f - 1) K'

set_option backward.isDefEq.respectTransparency false in
variable (p f) in
theorem apply_eq_pow_galFEquiv (σ : Gal(L/F)) (x : L) (h : x ^ (p ^ f - 1) = 1) :
    σ x = x ^ (galFEquiv p f K hζ σ).val.val := by
  let K' := (IsScalarTower.toAlgHom ℚ K L).fieldRange
  have : IsCyclotomicExtension {p ^ f - 1} ℚ K' := .equiv _ ℚ K
    (IsScalarTower.toAlgHom ℚ K L).equivFieldRange
  have := IsCyclotomicExtension.isAbelianGalois {p ^ f - 1} ℚ K'
  have hx : x ∈ K' := by
    rw [← orderOf_dvd_iff_pow_eq_one] at h
    have : NeZero (orderOf x) := ⟨by
      by_contra! h
      aesop⟩
    have : IsCyclotomicExtension {orderOf x} ℚ ℚ⟮x⟯ :=
      (IsPrimitiveRoot.orderOf x).intermediateField_adjoin_isCyclotomicExtension ℚ
    refine adjoin_simple_le_iff.mp ?_
    exact isCyclotomicExtension_le_of_dvd ℚ L (orderOf x) (p ^ f - 1) ℚ⟮x⟯ K' h
  let y : K' := ⟨x, hx⟩
  have := AlgEquiv.restrictNormalHom_apply K' (σ.restrictScalars ℚ) ⟨x, hx⟩
  erw [← this]
  simp [galFEquiv]
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (p ^ f - 1)]
  rfl
  simpa [y, Subtype.ext_iff]

example [hp' : Fact (Odd p)] [P.LiesOver 𝒑] (σ : Gal(L/F)) :
    σ (GaussSum hbij hζ 1) = GaussSum hbij hζ (galFEquiv p f K hζ σ).val.val := by
  simp_rw [GaussSum, gaussSum, MulChar.ringHomComp_apply, map_sum, map_mul,
    ← IsScalarTower.algebraMap_apply]
  refine Fintype.sum_congr _ _ fun x ↦ ?_
  congr 1
  · have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
    simp only [Int.reduceNeg, zpow_neg, zpow_one]
    rw [MulChar.inv_apply', ← MulChar.ringHomComp_apply, ← MulChar.ringHomComp_apply,
      ← AlgEquiv.coe_ringEquiv', ← RingEquiv.coe_toRingHom,
      map_teichmuller_apply_eq_pow hbij _ (galFEquiv p f K hζ σ).val.val _ hη,
      ← MulChar.ringHomComp_inv, ← MulChar.inv_apply', zpow_natCast]
    · simp
      rw [toto p f]
    · have : Nontrivial (ZMod (p ^ f - 1)) := by
        have := three_le_p_pow p f
        exact ZMod.nontrivial_iff.mpr (by aesop)
      exact (ZMod.val_ne_zero _).mpr <| Units.ne_zero (galFEquiv p f σ)
  · simp_rw [addCharTrace_apply, map_pow, ← algebraMap_zeta₀ p (isPrimitiveRoot_zeta₀ p hζ),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F L, AlgEquiv.commutes]
