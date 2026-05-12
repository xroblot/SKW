module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

public import SKW.Stickelberger.AddCharTrace
public import SKW.Stickelberger.Teichmuller

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

theorem not_dvd_pow_self_sub_one [hp : Fact (p.Prime)] : ¬ p ∣ p ^ f - 1 := by
  rw [Nat.dvd_sub_iff_right NeZero.one_le (p.div_pow_of_pos f _), Nat.dvd_one]
  · exact hp.out.ne_one
  · by_contra! h
    aesop

variable {p f}

variable {L : Type*} [Field L] [NumberField L] {F K : IntermediateField ℚ L} {P : Ideal (𝓞 K)}

variable (hbij : Function.Bijective (rootsOfUnity.mapQuot (p ^ f - 1) P))

variable {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p) [IsCyclotomicExtension {p} ℚ F]
    {η : 𝓞 K} (hη : IsPrimitiveRoot η (p ^ f - 1)) [IsCyclotomicExtension {p ^ f - 1} ℚ K]

variable (𝓟 : Ideal (𝓞 L))

theorem teichmuller_pow_comp_algebraMap_ne_one (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    (teichmuller hbij ^ a).ringHomComp (algebraMap (𝓞 K) (𝓞 L)) ≠ 1 := by
  have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
  rwa [← MulChar.ringHomComp_zpow, ne_eq, ← orderOf_dvd_iff_zpow_eq_one, ← MulChar.ringHomCompHom_apply,
    orderOf_injective (MulChar.ringHomCompHom (algebraMap (𝓞 K) (𝓞 L)))
    (MulChar.injective_ringHomComp (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))),
    orderOf_teichmuller hbij hη]

theorem teichmuller_ne_one [Fact (p.Prime)] [Fact (Odd p)] : teichmuller hbij ≠ 1 := by
  have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
  rw [ne_eq, ← orderOf_eq_one_iff, orderOf_teichmuller hbij hη, Nat.pred_eq_succ_iff, zero_add]
  exact ne_of_gt <| three_le_p_pow _ _

variable [P.IsMaximal]

local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

variable [hp : Fact (p.Prime)] [𝓟.IsPrime]

local instance : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite _

local instance [hP : P.LiesOver 𝒑] : ExpChar (𝓞 K ⧸ P) p := by
  have := Ideal.ringChar_quot P
  rw [← (liesOver_iff _ _).mp hP, absNorm_eq_card, Int.card_ideal_quot, ringChar.eq_iff] at this
  apply expChar_prime

include hζ in
theorem zeta_sub_one_mem [𝓟.LiesOver 𝒑] : algebraMap (𝓞 F) (𝓞 L) ζ - 1 ∈ 𝓟 := by
  rw [← map_one (f := algebraMap (𝓞 F) (𝓞 L)), ← map_sub, ← mem_comap,
    ← Ideal.under_def, IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p F
      (IsPrimitiveRoot.coe_submonoidClass_iff.mpr hζ) (under (𝓞 F) 𝓟)]
  exact Submodule.mem_span_singleton_self _

variable (f) in
theorem ramificationIdx_eq_p_sub_one [𝓟.LiesOver 𝒑] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    𝒑.ramificationIdx 𝓟 = p - 1 := by
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq (p * (p ^ f - 1)) L 𝓟 _
    (not_dvd_pow_self_sub_one p f), pow_zero, one_mul]
  rw [zero_add, pow_one]

variable (p f P) in
theorem ramificationIdx_eq_p_sub_one' [𝓟.LiesOver P] [P.LiesOver 𝒑]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    P.ramificationIdx 𝓟 = p - 1 := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have := Ideal.ramificationIdx_algebra_tower' 𝒑 P 𝓟
  rwa [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P (not_dvd_pow_self_sub_one p f),
    ramificationIdx_eq_p_sub_one f 𝓟, one_mul, eq_comm] at this

variable (p f) in
theorem ramificationIdx_under_eq_one [𝓟.LiesOver 𝒑] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    (under (𝓞 F) 𝓟).ramificationIdx 𝓟 = 1 := by
  have := Ideal.ramificationIdx_algebra_tower' 𝒑 (under (𝓞 F) 𝓟) 𝓟
  rwa [ramificationIdx_eq_p_sub_one f, IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime,
    left_eq_mul₀] at this
  exact Nat.sub_ne_zero_iff_lt.mpr hp.out.one_lt

variable (p f P) in
theorem inertia_deg_eq [P.LiesOver 𝒑] : 𝒑.inertiaDeg P = f := by
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := p ^ f - 1) p K P]
  · rw [ZMod.orderOf_mod_self_pow_sub_one _ _ hp.out.one_lt]
  · exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp (coprime_pow_sub_one p f).symm

include hζ in
variable (p f P) in
omit [IsCyclotomicExtension {p ^ f - 1} ℚ K] [P.IsMaximal] in
theorem zeta_sub_one_not_mem_sq [𝓟.LiesOver P] [𝓟.LiesOver 𝒑]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    algebraMap (𝓞 F) (𝓞 L) ζ - 1 ∉ 𝓟 ^ 2:= by
  have h : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (span {ζ - 1}) ≠ ⊥ := by
    apply map_ne_bot_of_ne_bot
    simpa [sub_eq_zero] using hζ.ne_one hp.out.one_lt
  rw [← map_one (f := algebraMap (𝓞 F) (𝓞 L)), ← map_sub, ← dvd_span_singleton,
    ← Set.image_singleton, ← map_span, FiniteMultiplicity.pow_dvd_iff_le_multiplicity
    (IsDedekindDomain.finiteMulticity IsPrime.ne_top' h),
    ← IsDedekindDomain.ramificationIdx_eq_multiplicity h inferInstance,
    show span {ζ - 1} = under (𝓞 F) 𝓟 from
      (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p F
        (IsPrimitiveRoot.coe_submonoidClass_iff.mpr hζ) (under (𝓞 F) 𝓟)).symm ,
    ramificationIdx_under_eq_one p f]
  exact Nat.not_succ_le_self 1

def GaussSum [P.LiesOver 𝒑] (a : ℤ) : 𝓞 L :=
  gaussSum ((teichmuller hbij ^ (- a)).ringHomComp (algebraMap (𝓞 K) (𝓞 L)))
    ((algebraMap (𝓞 F) (𝓞 L)).compAddChar (addCharTrace P hζ))

include hη in
omit [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p ^ f - 1} ℚ K] in
theorem GaussSum_periodic [P.LiesOver 𝒑] {k : ℤ} (hk : ↑(p ^ f - 1 : ℕ) ∣ k) (a : ℤ) :
    GaussSum hbij hζ (a + k) = GaussSum hbij hζ a := by
  rw [GaussSum, GaussSum, neg_add, zpow_add,
    orderOf_dvd_iff_zpow_eq_one (i := -k).mp
      (by rwa [orderOf_teichmuller hbij hη, Int.dvd_neg]), mul_one]

theorem GaussSum_mem [𝓟.LiesOver 𝒑] [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    GaussSum hbij hζ a ∈ 𝓟 := by
  have h𝓟 := zeta_sub_one_mem hζ 𝓟
  simp_rw [← Quotient.eq_zero_iff_mem, GaussSum, gaussSum, map_sum, map_mul,
    algebraMap_com_addCharTrace, addCharTrace_mk_eq_one _ _ h𝓟, mul_one, ← map_sum]
  rw [MulChar.sum_eq_zero_of_ne_one (teichmuller_pow_comp_algebraMap_ne_one hbij (- a)
    (by rwa [Int.dvd_neg])), map_zero]

omit [NeZero (p ^ f - 1)] [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p ^ f - 1} ℚ K] in
theorem GaussSum_frob [P.LiesOver 𝒑] (a : ℤ) :
    GaussSum hbij hζ (p * a) = GaussSum hbij hζ a := by
  rw [GaussSum, GaussSum, gaussSum, gaussSum, eq_comm, ← (AlgEquiv.bijective _).sum_comp
    (e := FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) p)]
  refine Fintype.sum_congr _ _ fun x ↦ ?_
  rw [FiniteField.frobeniusAlgEquiv_apply, Fintype.card_eq_nat_card, Int.card_ideal_quot,
    MonoidHom.coe_compAddChar, Function.comp_apply, Function.comp_apply,
    addCharTrace_frob_apply, map_pow, ← MulChar.pow_apply' _ hp.out.ne_zero,
    MulChar.ringHomComp_pow, ← zpow_natCast, ← zpow_mul, neg_mul, mul_comm a]

omit [IsCyclotomicExtension {p} ℚ F] in
theorem GaussSum_mul_GaussSum_neg [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    GaussSum hbij hζ a * GaussSum hbij hζ (- a) =
      algebraMap (𝓞 K) (𝓞 L) ((teichmuller hbij ^ (- a)) (- 1)) * p ^ f := by
  rw [GaussSum, GaussSum, ← mul_gaussSum_inv_eq_gaussSum, algebraMap_com_addCharTrace,
    mul_right_comm, neg_neg, zpow_neg, ← MulChar.ringHomComp_inv, mul_assoc,
    gaussSum_mul_gaussSum_eq_card (teichmuller_pow_comp_algebraMap_ne_one hbij a ha)
    (addCharTrace_isPrimitive P (hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L)))),
    Fintype.card_eq_nat_card, ← absNorm_eq_card, absNorm_eq_pow_inertiaDeg' P hp.out,
    MulChar.ringHomComp_inv, MulChar.ringHomComp_apply, Nat.cast_pow, inertia_deg_eq p f P]

theorem norm_GaussSum [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    ∃ k : ℕ, 1 ≤ k ∧ (Algebra.norm ℤ (GaussSum hbij hζ a)).natAbs = p ^ k := by
  have := congr_arg (fun x ↦ Int.natAbs (Algebra.norm ℤ x)) <| GaussSum_mul_GaussSum_neg hbij hζ a ha
  dsimp at this
  rw [map_mul, map_mul, Int.natAbs_mul, Int.natAbs_mul,  show (p : 𝓞 L) = algebraMap ℤ (𝓞 L) p by simp,
    map_pow, Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis L),
    ← pow_mul, Int.natAbs_pow, Int.natAbs_natCast, ← isUnit_neg_one.unit_spec,
    NumberField.isUnit_iff_natAbs_norm.mp <| RingHom.isUnit_map (algebraMap (𝓞 K) (𝓞 L))
    <| isUnit_teichmuller_zpow_apply hbij (- a) isUnit_neg_one.unit, one_mul] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (Dvd.intro _ this)
  refine ⟨k, ?_, hk⟩
  obtain ⟨Q, hQ, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝒑
  by_contra!
  refine Ideal.IsMaximal.ne_top hQ ?_
  refine Ideal.eq_top_of_isUnit_mem _ (GaussSum_mem hbij hζ Q a ha) ?_
  rw [isUnit_iff_natAbs_norm, hk, Nat.lt_one_iff.mp this, pow_zero]

theorem GaussSum_ne_zero [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    GaussSum hbij hζ a ≠ 0 := by
  rw [← Algebra.norm_ne_zero_iff (R := ℤ), ← Int.natAbs_ne_zero]
  obtain ⟨k, hk, hk'⟩ := norm_GaussSum hbij hζ a ha
  have := hp.out
  aesop

set_option synthInstance.maxHeartbeats 30000 in
omit [NeZero (p ^ f - 1)] [IsCyclotomicExtension {p ^ f - 1} ℚ K] [𝓟.IsPrime] in
theorem mk_sq_gausssum_eq_aux [DecidableEq (𝓞 K ⧸ P)] [(𝓟 ^ 2).LiesOver P]
    [(𝓟 ^ 2).LiesOver 𝒑] [P.LiesOver 𝒑] [(𝓟 ^ 2).LiesOver P] :
    ∑ x, Ideal.Quotient.mk (𝓟 ^ 2) (algebraMap (𝓞 K) (𝓞 L) ((teichmuller hbij) ⁻¹ x)) *
      algebraMap (ℤ ⧸ 𝒑) (𝓞 L ⧸ 𝓟 ^ 2) (Algebra.trace (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) x) = - 1 := by
  simp_rw [Ideal.Quotient.mk_algebraMap, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2),
    Quotient.algebraMap_eq, MulChar.inv_apply', teichmuller_mk_eq,
    IsScalarTower.algebraMap_apply (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2),
    FiniteField.algebraMap_trace_eq_sum_pow, ← map_mul, Finset.mul_sum]
  rw [← map_sum, Finset.sum_comm]
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
    pow_zero, Nat.sub_self, if_pos (Nat.dvd_zero _), Finset.sum_eq_zero, zero_add, map_neg, map_one]
  intro i hi
  rw [if_neg]
  rw [Fintype.card_eq_nat_card, ← Ideal.absNorm_eq_card, Int.card_ideal_quot,
    Ideal.absNorm_eq_pow_inertiaDeg' P hp.out]
  apply Nat.not_dvd_of_pos_of_lt
  · rw [Nat.sub_pos_iff_lt]
    exact Nat.one_lt_pow i.succ_ne_zero hp.out.one_lt
  · gcongr
    · exact NeZero.one_le
    · exact hp.out.one_lt
    · rwa [Nat.pred_eq_sub_one, Finset.mem_range, ← Nat.add_lt_iff_lt_sub_right] at hi

variable [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]

theorem mk_sq_gausssum_eq [hp' : Fact (Odd p)] [𝓟.LiesOver P] [P.LiesOver 𝒑] :
    Ideal.Quotient.mk (𝓟 ^ 2) (GaussSum hbij hζ 1) = -(algebraMap (𝓞 F) (𝓞 L) ζ - 1 :) := by
  classical
  have hζ₀ := hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))
  have : 3 ≤ p := (Nat.Prime.odd_iff hp.out).mp hp'.out
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have : (𝓟 ^ 2).LiesOver P := by
    refine pow_liesOver_of_liesOver P 𝓟 ?_
    rw [ramificationIdx_eq_p_sub_one' p f]
    grind
  have : (𝓟 ^ 2).LiesOver 𝒑 := LiesOver.trans (𝓟 ^ 2) P 𝒑
  have h𝓟 := zeta_sub_one_mem hζ 𝓟
  have h : (teichmuller hbij)⁻¹ ≠ 1 := by
    have hη := (IsCyclotomicExtension.zeta_spec (p ^ f - 1) ℚ K).toInteger_isPrimitiveRoot
    refine inv_ne_one.mpr ?_
    exact teichmuller_ne_one hbij
  simp_rw [GaussSum, gaussSum, zpow_neg, zpow_one, MulChar.ringHomComp_apply, map_sum, map_mul,
    algebraMap_com_addCharTrace, addCharTrace_mk_sq_eq P hζ₀ h𝓟, mul_add, mul_one,
    Finset.sum_add_distrib, ← map_sum, MulChar.sum_eq_zero_of_ne_one h, map_zero, zero_add,
    Algebra.smul_def, ← mul_assoc, ← Finset.sum_mul, mk_sq_gausssum_eq_aux]
  simp

variable (p f)

include p f in
set_option backward.isDefEq.respectTransparency false in
theorem K_sup_F_eq_top : K ⊔ F = (⊤ : IntermediateField ℚ L) := by
  have : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ (⊤ : IntermediateField ℚ L) :=
      IsCyclotomicExtension.equiv _ _ _ topEquiv.symm
  have : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ ↥(K ⊔ F) := by
        rw [mul_comm, ← Nat.Coprime.lcm_eq_mul (coprime_pow_sub_one p f)]
        exact isCyclotomicExtension_lcm_sup ℚ L (p ^ f - 1) p K F
  exact isCyclotomicExtension_eq {p * (p ^ f - 1)}  ℚ L _ _

include p f in
omit [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] in
theorem K_inf_F_eq_bot : K ⊓ F = ⊥ := by
  apply LinearDisjoint.inf_eq_bot
  exact IsCyclotomicExtension.Rat.linearDisjoint_ofCoprime (p ^ f - 1) p K F
    (coprime_pow_sub_one p f)

set_option backward.isDefEq.respectTransparency false in
variable (K) in
def galFEquiv : Gal(L/F) ≃* (ZMod (p ^ f - 1))ˣ :=
  haveI := IsCyclotomicExtension.isAbelianGalois {p * (p ^ f - 1)} ℚ L
  (MulEquiv.ofBijective (IntermediateField.restrictRestrictAlgEquivMapHom ℚ K F L)
    ⟨restrictRestrictAlgEquivMapHom_injective _ _ (K_sup_F_eq_top p f),
    restrictRestrictAlgEquivMapHom_surjective K F (K_inf_F_eq_bot p f)⟩).trans <|
      IsCyclotomicExtension.Rat.galEquivZMod (p ^ f - 1) K

theorem galFEquiv_val_ne_zero [Fact (Odd p)] (σ : Gal(L/F)) :
    (galFEquiv p f K σ).val.val ≠ 0 := by
  have : Nontrivial (ZMod (p ^ f - 1)) := by
    have := three_le_p_pow p f
    exact ZMod.nontrivial_iff.mpr (by aesop)
  exact (ZMod.val_ne_zero _).mpr <| Units.ne_zero (galFEquiv p f K σ)

include hη in
set_option backward.isDefEq.respectTransparency false in
theorem galLF_apply_eta (σ : Gal(L/F)) :
    σ • (algebraMap (𝓞 K) (𝓞 L) η) = (algebraMap (𝓞 K) (𝓞 L)) η ^ (galFEquiv p f K σ).val.val := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p ^ f - 1} ℚ K
  convert RingHom.congr_arg (algebraMap (𝓞 K) (𝓞 L))
    <| IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq (p ^ f - 1) K
    (AlgEquiv.restrictNormalHom K (AlgEquiv.restrictScalars ℚ σ)) hη.pow_eq_one
  apply FaithfulSMul.algebraMap_injective (𝓞 L) L
  rw [algebraMap.smul', AlgEquiv.smul_def, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 K) K L]
  exact (AlgEquiv.restrictNormalHom_apply K (AlgEquiv.restrictScalars ℚ σ) η).symm

include hη in
theorem galLF_apply_teichmuller_inv [Fact (Odd p)] (σ : Gal(L/F)) (x : 𝓞 K ⧸ P) :
    σ • ((teichmuller hbij)⁻¹.ringHomComp (algebraMap (𝓞 K) (𝓞 L)) x) =
      ((teichmuller hbij) ^ (- (galFEquiv p f K σ).val.val : ℤ)).ringHomComp
        (algebraMap (𝓞 K) (𝓞 L)) x := by
  rw [smul_eq_galRestrict_apply (𝓞 F) σ, zpow_neg, ← MulChar.ringHomComp_inv, ← MulChar.ringHomComp_inv,
    MulChar.inv_apply', MulChar.inv_apply', map_teichmuller_apply_eq_pow hbij _ _
      (galFEquiv p f K σ).val.val (galFEquiv_val_ne_zero p f σ) hη, zpow_natCast]
  rw [← smul_eq_galRestrict_apply, galLF_apply_eta p f hη]

omit [IsCyclotomicExtension {p} ℚ F] [P.IsMaximal] in
theorem galLF_apply_addCharTrace [P.LiesOver 𝒑] (σ : Gal(L/F)) (x : 𝓞 K ⧸ P) :
    σ • ((algebraMap (𝓞 F) (𝓞 L)).compAddChar (addCharTrace P hζ) x) =
      (algebraMap (𝓞 F) (𝓞 L)).compAddChar (addCharTrace P hζ) x := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_addCharTrace_eq_pow P hζ x
  simp [smul_eq_galRestrict_apply (𝓞 F) σ, Function.comp_apply, ha]

variable {p f}

include hη in
theorem gal_gaussSum_eq_gaussSum [Fact (Odd p)] [P.LiesOver 𝒑] (σ : Gal(L/F)) :
    σ • GaussSum hbij hζ 1 = GaussSum hbij hζ (galFEquiv p f K σ).val.val := by
  simp_rw [GaussSum, gaussSum, Finset.smul_sum, smul_mul', zpow_neg_one,
    galLF_apply_teichmuller_inv p f hbij hη, galLF_apply_addCharTrace]

def JacobiSum (a b : ℤ) : 𝓞 K := jacobiSum (teichmuller hbij ^ (-a)) (teichmuller hbij ^ (-b))

omit [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] in
theorem GaussSum_mul_GaussSum [P.LiesOver 𝒑] (a b : ℤ) (h : ¬ ↑(p ^ f - 1 : ℕ) ∣ a + b):
    GaussSum hbij hζ a * GaussSum hbij hζ b =
      GaussSum hbij hζ (a + b) * algebraMap (𝓞 K) (𝓞 L) (JacobiSum hbij a b) := by
  rw [GaussSum, GaussSum, GaussSum, ← jacobiSum_mul_nontrivial, ← MulChar.ringHomComp_mul,
    ← zpow_add, neg_add, jacobiSum_ringHomComp, JacobiSum]
  rw [← MulChar.ringHomComp_mul, ← zpow_add, ← neg_add]
  exact teichmuller_pow_comp_algebraMap_ne_one hbij _ (by rwa [Int.dvd_neg])

include hζ in
omit [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] in
theorem JacobiSum_ne_zero [P.LiesOver 𝒑] (a b : ℤ) (h : ¬ ↑(p ^ f - 1 : ℕ) ∣ a + b)
    (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) (hb : ¬ ↑(p ^ f - 1 : ℕ) ∣ b) :
    JacobiSum hbij a b ≠ 0 := by
  have hnz : GaussSum hbij hζ a * GaussSum hbij hζ b ≠ 0 :=
    mul_ne_zero (GaussSum_ne_zero hbij hζ a ha) (GaussSum_ne_zero hbij hζ b hb)
  rw [GaussSum_mul_GaussSum _ _ _ _ h, mul_ne_zero_iff] at hnz
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mp hnz.2
