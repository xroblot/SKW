module

public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.KummerExtension
public import SKW.Prereqs.OtherPR

public import Mathlib.Algebra.FiniteSupport.Basic

@[expose] public section

/-!
# Basic setup for the Kronecker-Weber theorem

Let `p` be an odd prime and `K/ℚ` a cyclic extension of degree `p` unramified outside `p`.
Set `F = ℚ(ζ_p)` and `L = KF`.

This file establishes
- `kw_kummer`: `L/F` is a Kummer extension `F(ᵖ√μ)` for some `μ ∈ 𝓞_F`, unramified outside `p`.
- `kw_abelian_kummer`: The Kummer criterion for `L/ℚ` to be abelian.
- `kw_split_prime`: Primes `𝔮` with `p ∤ v_𝔮(μ)` split completely in `F/ℚ`.
- `kw_mu_val_p`: For every prime `𝔮` of `F`, `p ∣ v_𝔮(μ)`.
- `kw_mu_pth_power_ideal`: `(μ) = 𝔞ᵖ` for some ideal `𝔞` of `𝓞_F`.
-/

open NumberField Ideal Polynomial Pointwise IntermediateField Module IsCyclotomicExtension
  nonZeroDivisors

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [Field L] [NumberField L]
variable (F : IntermediateField ℚ L) [IsCyclotomicExtension {p} ℚ F]
variable (K : IntermediateField ℚ L)

/-- `K/ℚ` is unramified outside `p`: every prime `q ≠ p` is unramified in `𝓞 K`. -/
def UnramifiedOutside (K : Type*) [Field K] (p : ℕ) : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})

set_option backward.isDefEq.respectTransparency false in
lemma kw_kummer₀ [IsGalois ℚ K] (hK : Module.finrank ℚ K = p) (htop : K ⊔ F = ⊤) :
    IsGalois F L ∧ IsCyclic Gal(L/F) ∧ finrank F L = p := by
  have hFL : IsGalois F L := IsGalois.sup_right K F htop
  have hF := Nat.totient_prime hp.out ▸ IsCyclotomicExtension.Rat.finrank p F
  have hdisj : K.LinearDisjoint F := by
    rw [LinearDisjoint.iff_inf_eq_bot, ← IntermediateField.finrank_eq_one_iff]
    have : p.Coprime (p - 1) := by have := hp.out.one_le; aesop
    have h₁ : finrank ℚ ↑(K ⊓ F) ∣ p := by
      rw [← hK]
      apply finrank_dvd_of_le_right inf_le_left
    have h₂ : finrank ℚ ↑(K ⊓ F) ∣ p - 1 := by
      rw [← hF]
      apply finrank_dvd_of_le_right inf_le_right
    exact Nat.dvd_one.mp (this ▸ Nat.dvd_gcd h₁ h₂)
  have hrF : finrank F L = p := hK ▸ LinearDisjoint.finrank_right_eq_finrank hdisj htop
  have hCL : IsCyclic Gal(L/F) :=
    isCyclic_of_prime_card <| hrF ▸ IsGalois.card_aut_eq_finrank F L
  exact ⟨hFL, ⟨hCL, hrF⟩⟩

/-- `L` is unramified outside `p`. -/
lemma kw_kummer' (hKram : UnramifiedOutside K p) (htop : K ⊔ F = ⊤) :
    UnramifiedOutside L p := by
  intro q hq hqp
  have hq0 : span {(q : ℤ)} ≠ ⊥ := by simpa using hq.ne_zero
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one hq0]
  intro 𝔮 _ hlo
  haveI := hlo
  haveI : 𝔮.IsMaximal := ‹𝔮.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hq0 𝔮)
  have := Ideal.LiesOver.tower_bot 𝔮 (under (𝓞 K) 𝔮) (span {(q : ℤ)})
  have := Ideal.LiesOver.tower_bot 𝔮 (under (𝓞 F) 𝔮) (span {(q : ℤ)})
  refine Ideal.ramificationIdx_sup_eq_one htop (p := span {(q : ℤ)})
    (P₁ := under (𝓞 K) 𝔮) (P₂ := under (𝓞 F) 𝔮) ?_ ?_ hq0
  · have := IsMaximal.under (𝓞 K) 𝔮
    exact (hKram q hq hqp).ramificationIdx_eq_one hq0
      (Ideal.LiesOver.tower_bot 𝔮 (under (𝓞 K) 𝔮) (span {(q : ℤ)}))
  · have : Fact q.Prime := ⟨hq⟩
    have : ¬ q ∣ p := by rwa [Nat.prime_dvd_prime_iff_eq hq hp.out]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' _ _ hq0]
    exact Rat.ramificationIdx_eq_of_not_dvd q F (under (𝓞 F) 𝔮) this

variable [IsGalois F L] [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p)

include hrF in
/-- `L/F` is a Kummer extension: there exists `μ ∈ 𝓞_F` such that `L = F(ᵖ√μ)`. -/
lemma kw_kummer [IsGalois ℚ K] (hK : Module.finrank ℚ K = p) :
    ∃ μ : 𝓞 F, μ ≠ 0 ∧
      IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ)) := by
  have hne : (primitiveRoots (Module.finrank F L) F).Nonempty :=
    hrF ▸ primitiveRoots_nonempty p ℚ F
  obtain ⟨α, ⟨x, hx₁⟩, hx₂⟩ := exists_root_adjoin_eq_top_of_isCyclic F L hne
  obtain ⟨d, hd₁, ⟨μ, hμ⟩⟩ := exists_integer_multiple x
  refine ⟨d ^ (finrank F L - 1) * μ, ?_, ?_⟩
  · refine mul_ne_zero (by aesop) ?_
    contrapose! hx₂
    rw [hx₂, map_zero, eq_comm, mul_eq_zero_iff_left (Int.cast_ne_zero.mpr hd₁)] at hμ
    rw [hμ, map_zero, eq_comm, pow_eq_zero_iff finrank_pos.ne'] at hx₁
    rw [hx₁, adjoin_zero, Ne.eq_def, bot_eq_top_iff_finrank_eq_one, hrF]
    exact hp.out.ne_one
  · have : F⟮d * α⟯ = ⊤ := by
      rw [← hx₂]
      apply le_antisymm
      · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
        exact IntermediateField.mul_mem _ (intCast_mem _ d) (mem_adjoin_simple_self _ α)
      · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
        have := div_mem (mem_adjoin_simple_self _ (d * α)) (intCast_mem F⟮d * α⟯ d)
        rwa [mul_div_cancel_left₀] at this
        exact Int.cast_ne_zero.mpr hd₁
    rw [← hrF]
    refine isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hne ?_ this
    rw [map_mul, hμ, map_mul, map_mul, map_pow, map_pow, map_intCast, map_intCast, ← mul_assoc,
      ← pow_succ, hx₁, Nat.sub_add_cancel finrank_pos, mul_pow]

variable [hQL : IsAbelianGalois ℚ L] {μ : 𝓞 F} (hμ : μ ≠ 0)
  [hS : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))]
  (hIrr:  Irreducible (X ^ p - C ((algebraMap (𝓞 F) F) μ)))

omit hCF hQL [IsGalois F L] in
include hrF hIrr in
lemma exists_pth_root :
    ∃ (α : 𝓞 L), α ≠ 0 ∧ algebraMap (𝓞 F) (𝓞 L) μ = α ^ p := by
  have hF : (primitiveRoots p F).Nonempty := primitiveRoots_nonempty p ℚ F
  have hβ := rootOfSplitsXPowSubC_pow (n := p) (algebraMap (𝓞 F) F μ) L
  obtain ⟨α, hα⟩ : ∃ α : 𝓞 L, (rootOfSplitsXPowSubC (NeZero.pos p) (μ : F) L) =
      algebraMap (𝓞 L) L α := by
    refine ⟨⟨rootOfSplitsXPowSubC (NeZero.pos p) (μ : F) L, ?_⟩, rfl⟩
    rw [mem_integralClosure_iff, ← IsIntegral.pow_iff (NeZero.pos p)]
    rw [hβ, ← IsScalarTower.algebraMap_apply]
    exact (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mpr <|
      RingOfIntegers.isIntegral μ
  refine ⟨α, ?_, ?_⟩
  · have := adjoin_root_eq_top_of_isSplittingField hF hIrr hβ
    contrapose! this
    rw [hα, this, map_zero, adjoin_zero, Ne.eq_def, bot_eq_top_iff_finrank_eq_one, hrF]
    exact hp.out.ne_one
  · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, ← hα, rootOfSplitsXPowSubC_pow, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

include hIrr hrF in
/-- The abelianity criterion for the Kummer extension `L = F(ᵖ√μ)` over `ℚ`. -/
-- FIXME: see if exists_pth_root can help
lemma kw_abelian_kummer (σ : Gal(F/ℚ)) :
    ∃ (ξ : F), ξ ≠ 0 ∧ σ (algebraMap (𝓞 F) F μ) = ξ ^ p * μ ^ (Rat.galEquivZMod p F σ).val.val := by
  have : IsGalois ℚ F := isGalois {p} ℚ F
  have hF : (primitiveRoots p F).Nonempty := primitiveRoots_nonempty p ℚ F
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := Gal(L/F))
  have : (σ.liftNormal L) * (τ.restrictScalars ℚ) = (τ.restrictScalars ℚ) * (σ.liftNormal L) :=
    mul_comm' _ _
  let α := rootOfSplitsXPowSubC hp.out.pos (μ : F) L
  let ζ := autEquivRootsOfUnity hF hIrr L τ
  have hτα : τ α = ζ • α := by rw [autEquivRootsOfUnity_apply_rootOfSplit hF hIrr]
  have hα : α ^ p = algebraMap (𝓞 F) L μ := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F L, rootOfSplitsXPowSubC_pow]
  have hα₀ : α ≠ 0 := by
    have := adjoin_root_eq_top_of_isSplittingField hF hIrr hα
    contrapose! this
    rw [this, adjoin_zero, Ne.eq_def, bot_eq_top_iff_finrank_eq_one, hrF]
    exact hp.out.ne_one
  have hζ : IsPrimitiveRoot ζ.val.val p := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    rw [orderOf_eq_card_of_forall_mem_zpowers hτ, IsGalois.card_aut_eq_finrank, hrF]
  have hmain := AlgEquiv.congr_fun this <| rootOfSplitsXPowSubC hp.out.pos (μ : F) L
  simp only [AlgEquiv.mul_apply, AlgEquiv.coe_restrictScalars'] at hmain
  rw [hτα, MulAction.subgroup_smul_def, Units.smul_def, Algebra.smul_def, map_mul,
    AlgEquiv.liftNormal_commutes, Rat.galEquivZMod_apply_of_pow_eq p _ _ hζ.pow_eq_one, map_pow] at hmain
  obtain ⟨c, j, hj, h⟩ := exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap hF hIrr (α := α)
    (β := σ.liftNormal L α) (by rw [rootOfSplitsXPowSubC_pow])
    (by rw [← map_pow, hα, IsScalarTower.algebraMap_apply (𝓞 F) F, AlgEquiv.liftNormal_commutes])
  have hc : algebraMap F L c ≠ 0 := by
    contrapose! hα₀
    rwa [hα₀, zero_mul, map_eq_zero] at h
  rw [h, map_mul, map_pow, hτα, AlgEquiv.commutes, MulAction.subgroup_smul_def, Units.smul_def,
    Algebra.smul_def, mul_pow, ← mul_assoc, ← mul_assoc, mul_left_inj' (pow_ne_zero j hα₀), mul_comm,
    mul_right_inj' hc, ← map_pow, ← map_pow, (FaithfulSMul.algebraMap_injective F L).eq_iff] at hmain
  refine ⟨c, by rwa [_root_.map_ne_zero] at hc, ?_⟩
  apply FaithfulSMul.algebraMap_injective F L
  rw [← AlgEquiv.liftNormal_commutes, ← rootOfSplitsXPowSubC_pow (n := p) (algebraMap (𝓞 F) F μ) L,
    map_pow, h, mul_pow, pow_right_comm, map_mul, map_pow, map_pow, rootOfSplitsXPowSubC_pow,
    hζ.pow_inj (ZMod.val_lt _) hj hmain]

variable [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]

include hμ hrF hIrr in
/-- If `𝔮` is a prime ideal of `𝓞_F` with `p ∤ v_𝔮(μ)` and `L/ℚ` is abelian, then `𝔮` splits
completely in `F/ℚ`: every `σ ∈ Gal(F/ℚ)` with `σ • 𝔮 = 𝔮` is the identity. -/
lemma kw_split_prime {𝔮 : Ideal (𝓞 F)} (h𝔮 : Prime 𝔮) (hv : ¬ p ∣ multiplicity 𝔮 (span {(μ : 𝓞 F)}))
    {σ : Gal(F/ℚ)} (hσ : σ • 𝔮 = 𝔮) :
    σ = 1 := by
  obtain ⟨𝔞, h𝔞⟩ := pow_multiplicity_dvd 𝔮 (span {(μ : 𝓞 F)})
  obtain ⟨ξ, hξ₀, hξ⟩ := kw_abelian_kummer p F hrF hIrr σ
  obtain ⟨d, hd₀, ⟨β, hβ⟩⟩ := exists_integer_multiple ξ
  have hβ₀ : β ≠ 0 := by
    by_contra!
    simp [this, hd₀, hξ₀] at hβ
  replace hβ : σ • (d ^ p * μ) = β ^ p * μ ^ (Rat.galEquivZMod p F σ).val.val := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, MulSemiringAction.smul_mul, map_mul, algebraMap.smul', algebraMap.smul', map_pow,
      map_intCast, AlgEquiv.smul_def, map_pow, map_intCast, AlgEquiv.smul_def, hξ, map_pow, hβ,
      ← mul_assoc, ← mul_pow, map_pow]
  have hf𝔮 : FiniteMultiplicity 𝔮 𝔮 := FiniteMultiplicity.of_prime_left h𝔮 h𝔮.ne_zero
  have hfμ : FiniteMultiplicity 𝔮 (span {μ}) := FiniteMultiplicity.of_prime_left h𝔮 <| by simpa using hμ
  have hfβ : FiniteMultiplicity 𝔮 (span {β}) := FiniteMultiplicity.of_prime_left h𝔮 <| by simpa using hβ₀
  have hσ𝔞 : multiplicity 𝔮 (σ • 𝔞) = 0 := by
    rw [← hσ, pointwise_smul_def', pointwise_smul_def', multiplicity_map_eq]
    have := congr_arg (multiplicity 𝔮 · ) h𝔞
    rwa [multiplicity_mul h𝔮 (by rwa [← h𝔞]), hf𝔮.multiplicity_pow h𝔮, multiplicity_self,
      mul_one, Nat.left_eq_add] at this
  have hσ𝔞₀ : σ • 𝔞 ≠ 0 := by
    contrapose! hσ𝔞
    simp [hσ𝔞]
  have h₁ := congr_arg (multiplicity 𝔮 · ) <| congr_arg (σ • · ) <|
    congr_arg (span {(d ^ p : 𝓞 F)} * · ) h𝔞
  rw [span_singleton_mul_span_singleton, smul_mul', multiplicity_mul h𝔮, smul_mul', smul_pow', hσ,
    multiplicity_mul h𝔮, smul_span, smul_span, smul_pow', ← span_singleton_pow,
    FiniteMultiplicity.multiplicity_pow h𝔮, multiplicity_pow_self h𝔮.ne_zero h𝔮.not_unit, hβ,
    ← span_singleton_mul_span_singleton, multiplicity_mul h𝔮, ← span_singleton_pow,
    ← span_singleton_pow, FiniteMultiplicity.multiplicity_pow h𝔮 hfβ,
    FiniteMultiplicity.multiplicity_pow h𝔮 hfμ, hσ𝔞, add_zero] at h₁
  replace h₁ := congr_arg ((↑) : _ → ZMod p) h₁
  simp only [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, ZMod.natCast_val, ZMod.cast_id', id_eq,
    zero_add] at h₁
  rw [mul_eq_right₀] at h₁
  · rwa [← (Rat.galEquivZMod p F).apply_eq_iff_eq, map_one, Units.ext_iff, Units.val_one]
  · rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  have h₃ := congr_arg ( · ^ (Rat.galEquivZMod p F σ).val.val) h𝔞
  · apply h𝔮.finiteMultiplicity_mul
    · exact span_singleton_pow β _ ▸ FiniteMultiplicity.pow h𝔮 hfβ
    · exact span_singleton_pow  μ _ ▸ FiniteMultiplicity.pow h𝔮 hfμ
  · exact FiniteMultiplicity.of_prime_left h𝔮 <| by simpa [smul_eq_zero_iff_eq]
  · apply h𝔮.finiteMultiplicity_mul
    · exact FiniteMultiplicity.pow h𝔮 hf𝔮
    · exact FiniteMultiplicity.of_prime_left h𝔮 hσ𝔞₀
  · apply h𝔮.finiteMultiplicity_mul
    · rw [← span_singleton_pow, smul_pow']
      refine FiniteMultiplicity.pow h𝔮 ?_
      exact FiniteMultiplicity.of_prime_left h𝔮 <| by simpa [smul_eq_zero_iff_eq]
    · rw [smul_mul', smul_pow', hσ]
      apply h𝔮.finiteMultiplicity_mul
      · exact FiniteMultiplicity.pow h𝔮 hf𝔮
      · exact FiniteMultiplicity.of_prime_left h𝔮 hσ𝔞₀

attribute [local instance] Ideal.Quotient.field in
omit [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)] in
include hrF hIrr hμ in
/-- For every prime `𝔮` of `𝓞_F`, `p ∣ v_𝔮(μ)`. -/
lemma kw_mu_val_p (𝔮 : Ideal (𝓞 F)) [𝔮.IsMaximal] (hLRam : UnramifiedOutside L p) (hp' : Odd p) :
    p ∣ multiplicity 𝔮 (span {μ}) := by
  let q := absNorm (under ℤ 𝔮)
  have : 𝔮.LiesOver (span {(q : ℤ)}) := Int.liesOver_span_absNorm 𝔮
  have h𝔮 : Prime 𝔮 := IsDedekindDomain.prime_of_maximal 𝔮
  have hq : Fact q.Prime := ⟨Nat.absNorm_under_prime 𝔮⟩
  by_cases hqp : q = p
  · obtain ⟨σ, hσ, hσ'⟩ : ∃ σ : Gal(F/ℚ), σ • 𝔮 = 𝔮 ∧ σ ≠ 1 := by
      have : 𝔮.LiesOver (span {(p : ℤ)}) := hqp ▸ Int.liesOver_span_absNorm 𝔮
      have : IsGalois ℚ F := isGalois {p} ℚ F
      have : Nontrivial (MulAction.stabilizer Gal(F/ℚ) 𝔮) := by
        rw [← Finite.one_lt_card_iff_nontrivial, card_stabilizer_eq (span {(p : ℤ)}) 𝔮,
          Rat.ramificationIdxIn_eq_of_prime, Rat.inertiaDegIn_eq_of_prime, mul_one]
        exact Nat.lt_sub_of_add_lt <| (Nat.Prime.odd_iff hp.out).mp hp'
      rwa [Subgroup.nontrivial_iff_exists_ne_one] at this
    contrapose! hσ'
    exact kw_split_prime p F hrF hμ hIrr h𝔮 hσ' hσ
  · obtain ⟨𝔔, _, _⟩  := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔮
    have : 𝔔.LiesOver (span {(q : ℤ)}) := LiesOver.trans 𝔔 𝔮 _
    have h𝔔 : Prime 𝔔 := IsDedekindDomain.prime_of_maximal 𝔔
    have h𝔔' : 𝔮.ramificationIdx 𝔔 = 1 := by
      have hram := (hLRam q hq.out hqp).ramificationIdx_eq_one (by simpa using hq.out.ne_zero)
        ‹𝔔.LiesOver (span {(q : ℤ)})›
      have htower := ramificationIdx_algebra_tower' (span {(q : ℤ)}) 𝔮 𝔔
      rw [hram, Ideal.ramificationIdx_eq_ramificationIdx' _ 𝔮 (by simpa using hq.out.ne_zero),
        IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q F 𝔮
          (by rwa [Nat.prime_dvd_prime_iff_eq hq.out hp.out]),
        one_mul] at htower
      linarith
    obtain ⟨α, hα₀, hα⟩ := exists_pth_root p F hrF hIrr
    have := IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul' (span {μ}) h𝔮.irreducible
      h𝔔.irreducible (IsMaximal.ne_bot_of_isIntegral_int 𝔔)
    rw [h𝔔', Nat.cast_one, one_mul, FiniteMultiplicity.emultiplicity_eq_multiplicity,
      FiniteMultiplicity.emultiplicity_eq_multiplicity, Nat.cast_inj, map_span, Set.image_singleton,
      hα, ← span_singleton_pow, FiniteMultiplicity.multiplicity_pow] at this
    · exact Dvd.intro _ this
    · exact h𝔔
    · exact FiniteMultiplicity.of_prime_left h𝔔 (by simpa)
    · exact FiniteMultiplicity.of_prime_left h𝔮 (by simpa)
    · exact FiniteMultiplicity.of_prime_left h𝔔 <| map_ne_bot_of_ne_bot (by simpa)

include hrF hμ hIrr in
/-- The ideal `(μ)` is a `p`-th power: `(μ) = 𝔞ᵖ` for some ideal `𝔞` of `𝓞_F`. -/
lemma kw_mu_pth_power_ideal (hLram : UnramifiedOutside L p) (hp' : Odd p) :
    ∃ 𝔞 : Ideal (𝓞 F), 𝔞 ≠ ⊥ ∧ 𝔞 ^ p = span {(μ : 𝓞 F)} := by
  have hsμ : span {μ} ≠ ⊥ := by simpa
  have := Ideal.finprod_heightOneSpectrum_pow_multiplicity hsμ
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ :=
    fun w ↦ (kw_mu_val_p p F hrF hμ hIrr w.asIdeal hLram hp').choose
  have hv {w} : multiplicity w.asIdeal (span {μ}) = p * v w :=
    (kw_mu_val_p p F hrF hμ hIrr w.asIdeal hLram hp').choose_spec
  have hv' : Function.HasFiniteMulSupport fun w ↦ w.asIdeal ^ v w := by
    have := Ideal.hasFiniteMulSupport hsμ
    simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hsμ, hv,
      mul_comm p, pow_mul] at this
    exact Function.HasFiniteMulSupport.of_comp this (one_pow _) (pow_left_injective hp.out.ne_zero)
  have := Ideal.finprod_heightOneSpectrum_pow_multiplicity hsμ
  simp only [hv, mul_comm p, pow_mul, ← finprod_pow hv'] at this
  exact ⟨_, by rwa [← zero_eq_bot, ← pow_ne_zero_iff hp.out.ne_zero, this], this⟩

include hrF hμ hIrr in
/-- One can choose ν such that the prime ideal above `p` does not divide `⟨ν⟩`. -/
lemma kw_not_dvd_nu (𝔭 : Ideal (𝓞 F)) [𝔭.IsMaximal] [𝔭.LiesOver (span {(p : ℤ)})]
    (hLram : UnramifiedOutside L p) (hp' : Odd p) :
    ∃ ν : 𝓞 F, ν ≠ 0 ∧ IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F ν)) ∧
      Irreducible (X ^ p - C ((algebraMap (𝓞 F) F) ν)) ∧
      multiplicity 𝔭 (span {ν}) = 0 := by
  let hζ := IsCyclotomicExtension.zeta_spec p ℚ F
  have hζ₀ : algebraMap (𝓞 F) F (hζ.toInteger - 1) ≠ 0 := by
    rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F), sub_ne_zero]
    exact hζ.toInteger_isPrimitiveRoot.ne_one hp.out.one_lt
  have h𝔭 := hζ.zeta_sub_one_prime'.isMaximal_span_singleton
  have hζ₁ : Prime (hζ.toInteger - 1) := hζ.zeta_sub_one_prime'
  have hsζ : Prime (span {hζ.toInteger - 1}) := prime_span_singleton_iff.mpr hζ₁
  have hF : (primitiveRoots p F).Nonempty := primitiveRoots_nonempty p ℚ F
  obtain ⟨ν, hν⟩ := pow_multiplicity_dvd (hζ.toInteger - 1) μ
  obtain ⟨k, hk⟩ := kw_mu_val_p p F hrF hμ hIrr (span {hζ.toInteger - 1}) hLram hp'
  let α := rootOfSplitsXPowSubC hp.out.pos (μ : F) L
  have hα : α ^ p = algebraMap (𝓞 F) L μ := by
        rw [IsScalarTower.algebraMap_apply (𝓞 F) F L, rootOfSplitsXPowSubC_pow]
  rw [multiplicity_span_span] at hk
  have hν₀ : ν ≠ 0 := by
    contrapose! hμ
    rwa [hμ, mul_zero] at hν
  refine ⟨ν, hν₀, ?_, ?_, ?_⟩
  · rw [hk, pow_mul, pow_right_comm] at hν
    rw [← hrF]
    apply isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top (hrF ▸ hF)
      (α := (algebraMap (𝓞 F) L) (hζ.toInteger - 1) ^ (- k : ℤ)  * α)
    · rw [mul_pow, hrF, rootOfSplitsXPowSubC_pow, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, hν, map_mul, map_pow, map_pow, ← zpow_natCast _ k,
        ← zpow_natCast _ p, ← zpow_mul, ← zpow_natCast _ p, ← zpow_mul, ← mul_assoc, ← zpow_add₀,
        neg_mul, neg_add_cancel, zpow_zero, one_mul]
      rwa [IsScalarTower.algebraMap_apply (𝓞 F) F, _root_.map_ne_zero]
    · rw [mul_comm, IsScalarTower.algebraMap_apply (𝓞 F) F L, ← map_zpow₀,
        adjoin_simple_mul _ _ (zpow_ne_zero _ hζ₀)]
      have hα : α ^ p = algebraMap (𝓞 F) L μ := by
        rw [IsScalarTower.algebraMap_apply (𝓞 F) F L, rootOfSplitsXPowSubC_pow]
      exact adjoin_root_eq_top_of_isSplittingField (hrF ▸ hF) hIrr hα
  · rw [hk, pow_mul, pow_right_comm] at hν
    rw [X_pow_sub_C_irreducible_iff_of_prime hp.out] at hIrr ⊢
    contrapose! hIrr
    obtain ⟨b, hb⟩ := hIrr
    refine ⟨(hζ.toInteger - 1) ^ k * b, by simp [hν, mul_pow, hb, map_mul]⟩
  · replace hν := congr_arg (span {·}) hν
    replace hν := congr_arg (emultiplicity (span {hζ.toInteger - 1}) · ) hν
    rwa [← span_singleton_mul_span_singleton, ← span_singleton_pow,
      emultiplicity_mul hsζ, emultiplicity_pow_self, emultiplicity_span_span,
      FiniteMultiplicity.emultiplicity_eq_multiplicity,
      FiniteMultiplicity.emultiplicity_eq_multiplicity, ← Nat.cast_add, Nat.cast_inj,
      Nat.left_eq_add, ← Rat.eq_span_zeta_sub_one_of_liesOver' p F hζ 𝔭] at hν
    · exact FiniteMultiplicity.of_prime_left hsζ (by simpa)
    · exact FiniteMultiplicity.of_prime_left hζ₁ hμ
    · simpa using RingOfIntegers.coe_ne_zero_iff.mp hζ₀
    · exact hsζ.not_unit

end
