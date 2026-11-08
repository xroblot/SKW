module

public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.FractionalIdeal
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.KummerExtension
public import SKW.Prereqs.OtherPR
public import SKW.Prereqs.Unramified
public import SKW.Prereqs.TameRamification
public import SKW.Stickelberger.Stickelberger

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.RingTheory.ClassGroup.Basic

set_option linter.style.header false

/-!
# The Kummer step of the Kronecker-Weber theorem

Let `p` be an odd prime, `F = ℚ(ζ_p)` and `L/F` a cyclic extension of degree `p`, with `L/ℚ`
abelian.

This file establishes
- `kw_kummer₀`: if `L/ℚ` is Galois of degree `p * (p - 1)`, then `L/F` is cyclic of degree `p`.
- `kw_kummer`: `L/F` is a Kummer extension `F(ᵖ√μ)` for some nonzero `μ ∈ F`.
- `kw_unit_eq_mul_pow`: a unit `η` of `F` with `η * conj η` a `p`-th power is a `p`-th root of
  unity times a `p`-th power.
- `kw_abelian_kummer`: the Kummer criterion for `L/ℚ` to be abelian.
- `kw_split_prime`: if `p ∤ v(μ)`, then the stabilizer of `v` in `Gal(F/ℚ)` is trivial.
- `kw_mu_val_p`: if `L/F` is unramified outside `p`, then `p ∣ v(μ)` for every prime `v` of `F`.
- `kw_mu_pth_power_ideal`: if `L/F` is unramified outside `p`, then `(μ) = 𝔞 ^ p` for some
  fractional ideal `𝔞` of `F`.
- `kw_class_trivial`: such an ideal `𝔞` is principal (Stickelberger).
- `kw_unit_conj_pow`: then `μ = β ^ p * η` for a unit `η` with `η * conj η` a `p`-th power.
- `kw_unit_root_of_unity`: then `L` is the cyclotomic extension `ℚ(ζ_{p²})`.
-/

@[expose] public section

open NumberField Ideal Polynomial Pointwise IntermediateField Module IsCyclotomicExtension
  nonZeroDivisors IsDedekindDomain FractionalIdeal

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime] {F : Type*} [Field F] [NumberField F] {L : Type*} [Field L]
  [Algebra F L]

section

variable [NumberField L] {μ : F} [IsSplittingField F L (X ^ p - C μ)]

/-- If `L` is unramified outside `p` and `v` is a prime of `𝓞 F` above a prime `q ≠ p`, then
`p ∣ v(μ)`. -/
lemma kw_mu_val_p_of_liesOver_ne {q : ℕ} [hq : Fact q.Prime] (hqp : q ≠ p)
    {v : HeightOneSpectrum (𝓞 F)} [v.asIdeal.LiesOver (span {(q : ℤ)})]
    (hLRam : UnramifiedOutside L p) :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (S := 𝓞 L) v
  have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    have : w.asIdeal.LiesOver v.asIdeal := by
      rw [← hw, HeightOneSpectrum.under_asIdeal, liesOver_iff]
    have := hLRam q hq.out hqp w.asIdeal w.isPrime <| Ideal.LiesOver.trans w.asIdeal v.asIdeal _
    rw [← Ideal.ramificationIdx_eq_one_iff, ramificationIdx_tower v.asIdeal] at this
    exact Nat.eq_one_of_mul_eq_one_left this
  have h_main := FractionalIdeal.count_extendedHom F L w ((spanSingleton (𝓞 F)⁰) μ)
  rw [hram, Nat.cast_one, one_mul, hw, extendedHom_spanSingleton,
    IsFractionRing.map_algebraMap_apply, ← rootOfSplitsXPowSubC_pow μ L (n := p), map_pow,
    count_pow] at h_main
  exact dvd_of_mul_right_eq _ h_main

end

variable [IsCyclotomicExtension {p} ℚ F]

variable (F) in
/-- If `L/ℚ` is Galois of degree `p * (p - 1)`, then `L/F` is cyclic Galois of degree `p`. -/
lemma kw_kummer₀ [NumberField L] [IsGalois ℚ L] (hL : finrank ℚ L = p * (p - 1)) :
    IsGalois F L ∧ IsCyclic Gal(L/F) ∧ finrank F L = p := by
  have hF : finrank ℚ F = p - 1 := Nat.totient_prime hp.out ▸ Rat.finrank p F
  have hrF : finrank F L = p := by
    have h := finrank_mul_finrank ℚ F L
    rw [hF, hL, mul_comm p (p - 1)] at h
    exact Nat.eq_of_mul_eq_mul_left (by have := hp.out.one_lt; lia) h
  have : IsGalois F L := IsGalois.tower_top_of_isGalois ℚ F L
  exact ⟨this, isCyclic_of_prime_card <| by rw [IsGalois.card_aut_eq_finrank, hrF], hrF⟩


open IsCMField in
/-- If `η * conj η` is a `p`-th power, then `η = ζ * δ ^ p` with `ζ ^ p = 1`. -/
lemma kw_unit_eq_mul_pow (hp' : Odd p) [IsCMField F] {η : (𝓞 F)ˣ} {w : F}
    (hη : ((η : 𝓞 F) : F) * complexConj F ((η : 𝓞 F) : F) = w ^ p) :
    ∃ ζ δ : F, ζ ^ p = 1 ∧ ((η : 𝓞 F) : F) = ζ * δ ^ p := by
  obtain ⟨ω, ε, hε, h⟩ := exists_torsion_realunits_pow_indexRealUnits_eq_mul η
  rw [Rat.indexRealUnits_eq_one' p _ (by grind), pow_one] at h
  obtain ⟨γ, hγ⟩ : ∃ γ : F, ε = γ ^ p := by
    have : η.val * (complexConj F) η.val = ε.val ^ 2 := by
      rw [← coe_ringOfIntegersComplexConj, ← coe_unitsComplexConj, ← Units.coe_mul, ← Units.coe_pow,
        RingOfIntegers.eq_iff, ← Units.ext_iff, h, map_mul, unitsComplexConj_torsion,
        (unitsComplexConj_eq_self_iff _ ε).mpr hε, Subgroup.coe_inv, mul_mul_mul_comm,
        mul_inv_cancel, one_mul, sq]
    refine ⟨w ^ Nat.gcdA 2 p * ε ^ Nat.gcdB 2 p, ?_⟩
    rw [mul_pow, ← zpow_natCast, zpow_comm, zpow_natCast, ← hη, this, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul', ← zpow_add₀ ε.coe_ne_zero, ← Nat.gcd_eq_gcd_ab,
      Nat.coprime_two_left.mpr hp', Nat.cast_one, zpow_one]
  have hω : (ω.val : F) ^ (2 * p) = 1 := by
    rw [show 2 * p = Nat.card (Units.torsion F) by
      rw [← Units.torsionOrder, Rat.torsionOrder_eq (n := p),
        ite_eq_right (Nat.not_even_iff_odd.mpr hp')], ← map_pow, ← Units.val_pow_eq_pow_val,
        ← SubmonoidClass.coe_pow, pow_card_eq_one', Subgroup.coe_one, Units.val_one, map_one]
  refine ⟨(ω.val : F) ^ (p + 1), ω.val * γ, ?_, ?_⟩
  · have h : (p + 1) * p = (2 * p) * ((p + 1) / 2) := by
      rw [mul_comm 2, mul_assoc, Nat.mul_div_eq_iff_dvd.mpr, mul_comm]
      grind
    rw [← pow_mul, h, pow_mul, hω, one_pow]
  · rw [mul_pow, ← mul_assoc, ← pow_add, show p + 1 + p = 2 * p + 1 by ring, pow_add, hω, one_mul,
      pow_one, ← hγ, ← map_mul, ← Units.val_mul, ← h]

section

variable [FiniteDimensional F L] [IsGalois F L] [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p)

include hrF in
/-- The extension `L/F` is a Kummer extension: `L` is the splitting field of `X ^ p - μ` for some
nonzero `μ ∈ F`. -/
theorem kw_kummer : ∃ μ : F, μ ≠ 0 ∧ IsSplittingField F L (X ^ p - C μ) := by
  have hne : (primitiveRoots (Module.finrank F L) F).Nonempty :=
    hrF ▸ primitiveRoots_nonempty p ℚ F
  obtain ⟨g, hg, ⟨μ, hμ₁⟩, hμ₂⟩ := exists_root_adjoin_eq_top_of_isCyclic' F L hne
  refine ⟨μ, ?_, ?_⟩
  · contrapose hg
    rwa [hg, map_zero, eq_comm, pow_eq_zero_iff finrank_pos.ne'] at hμ₁
  · exact hrF ▸ isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hne hμ₁.symm hμ₂

section

variable [NumberField L] [IsAbelianGalois ℚ L] {μ : F} [IsSplittingField F L (X ^ p - C μ)]
  (hIrr : Irreducible (X ^ p - C μ))

include hIrr hrF

/-- The Kummer criterion for `L/ℚ` to be abelian: every `σ ∈ Gal(F/ℚ)` sends `μ` to
`c ^ p * μ ^ a`, where `a` is the image of `σ` in `(ℤ/pℤ)ˣ`. -/
theorem kw_abelian_kummer (σ : Gal(F/ℚ)) :
    ∃ c : F, c ≠ 0 ∧ σ μ = c ^ p * μ ^ (Rat.galEquivZMod p F σ).val.val := by
  have hne : (primitiveRoots p F).Nonempty := primitiveRoots_nonempty p ℚ F
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  obtain ⟨τ, hτ⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hCF
  set a := rootOfSplitsXPowSubC hp.out.pos μ L
  have hμ : algebraMap F L μ = a ^ p := (rootOfSplitsXPowSubC_pow _ _).symm
  have ha₀ : a ≠ 0 := by
    contrapose hμ₀
    rw [← map_eq_zero (algebraMap F L), hμ, hμ₀, zero_pow hp.out.ne_zero]
  obtain ⟨c, j, hj, h⟩ := exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap hne hIrr (α := a)
    (β := σ.liftNormal L a) (by rw [rootOfSplitsXPowSubC_pow])
    (by rw [← map_pow, rootOfSplitsXPowSubC_pow, AlgEquiv.liftNormal_commutes])
  refine ⟨c, ?_, ?_⟩
  · contrapose ha₀
    rw [← map_eq_zero (σ.liftNormal L), h, ha₀, map_zero, zero_mul]
  · suffices (Rat.galEquivZMod p F σ).val = (j : ZMod p) by
      apply FaithfulSMul.algebraMap_injective F L
      rw [← AlgEquiv.liftNormal_commutes, hμ, map_pow, h, mul_pow, map_mul, map_pow, pow_right_comm,
        ← hμ, map_pow, this, ZMod.val_cast_of_lt hj]
    let ζ : F := (autEquivRootsOfUnity hne hIrr L τ).val
    have hζ : IsPrimitiveRoot ζ p := by
      rw [← hrF, ← IsGalois.card_aut_eq_finrank, ← hτ, IsPrimitiveRoot.iff_orderOf, orderOf_units,
        Subgroup.orderOf_coe]
      exact MulEquiv.orderOf_eq (autEquivRootsOfUnity hne hIrr L) τ
    rw [← Rat.apply_eq_pow_iff_galEquivZMod_eq hζ]
    have hτa : algebraMap F L ζ * a = τ.restrictScalars ℚ a := by
      rw [AlgEquiv.restrictScalars_apply, autEquivRootsOfUnity_apply_rootOfSplit hne hIrr,
        MulAction.subgroup_smul_def, Units.smul_def, Algebra.smul_def]
    apply FaithfulSMul.algebraMap_injective F L
    rw [ZMod.val_cast_of_lt hj, ← mul_left_inj' (by aesop : (σ.liftNormal L) a ≠ 0),
      ← AlgEquiv.liftNormal_commutes, ← map_mul, hτa, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      ← mul_smul, mul_comm', mul_smul, AlgEquiv.smul_def, AlgEquiv.smul_def, h, map_mul,
      AlgEquiv.restrictScalars_apply, AlgEquiv.commutes, map_pow, ← hτa, mul_pow, map_pow]
    ring

/-- If `v` is a prime of `𝓞 F` with `p ∤ v(μ)`, then every `σ ∈ Gal(F/ℚ)` fixing `v` is the
identity. -/
lemma kw_split_prime {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ)) {σ : Gal(F/ℚ)} (hσ : σ • v = v) :
    σ = 1 := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  apply (Rat.galEquivZMod p F).injective
  rw [map_one, Units.ext_iff, Units.val_one]
  obtain ⟨c, hc₀, hc₁⟩ := kw_abelian_kummer hrF hIrr σ
  have : count F v (spanSingleton (𝓞 F)⁰ μ) = count F v (spanSingleton (𝓞 F)⁰ (σ μ)) := by
    rw [← AlgEquiv.smul_def, ← spanSingleton_smul, ← FractionalIdeal.count_smul _ _ _ σ, hσ]
  have := congr_arg (· : ℤ → ZMod p) this
  rwa [hc₁, map_mul, map_pow, map_pow, count_mul _ _ (by simp [hc₀]) (by simp [hμ₀]), count_pow,
    count_pow, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
    Int.cast_mul, right_eq_mul₀, Int.cast_natCast, ZMod.natCast_zmod_val] at this
  rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If `v` is a prime of `𝓞 F` above `p`, then `p ∣ v(μ)`. -/
lemma kw_mu_val_p_of_liesOver (hp' : Odd p) {v : HeightOneSpectrum (𝓞 F)}
    [v.asIdeal.LiesOver (span {(p : ℤ)})] :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  have : IsGalois ℚ F := isGalois {p} ℚ F
  have : Nontrivial (MulAction.stabilizer Gal(F/ℚ) v.asIdeal) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [Ideal.card_stabilizer_eq (span {(p : ℤ)}), Rat.ramificationIdxIn_eq_of_prime,
      Rat.inertiaDegIn_eq_of_prime, mul_one]
    lia [hp.out.odd_iff.mp hp']
  obtain ⟨σ, hσ⟩ := exists_ne (1 : MulAction.stabilizer Gal(F/ℚ) v.asIdeal)
  by_contra hv
  refine hσ <| Subtype.ext <| kw_split_prime hrF hIrr hv ?_
  rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.smul_asIdeal, σ.prop]

/-- If `L` is unramified outside `p`, then `p ∣ v(μ)` for every prime `v` of `𝓞 F`. -/
lemma kw_mu_val_p (hp' : Odd p) (v : HeightOneSpectrum (𝓞 F)) (hLRam : UnramifiedOutside L p) :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  have : Fact (absNorm (under ℤ v.asIdeal)).Prime := ⟨Nat.absNorm_under_prime v.asIdeal⟩
  have hv : v.asIdeal.LiesOver (span {((absNorm (under ℤ v.asIdeal) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm v.asIdeal
  by_cases hqp : absNorm (under ℤ v.asIdeal) = p
  · rw [hqp] at hv
    exact kw_mu_val_p_of_liesOver hrF hIrr hp'
  · exact kw_mu_val_p_of_liesOver_ne hqp hLRam

/-- If `L` is unramified outside `p`, then `(μ) = 𝔞 ^ p` for a fractional ideal `𝔞` of `F`. -/
lemma kw_mu_pth_power_ideal (hp' : Odd p) (hLRam : UnramifiedOutside L p) :
    ∃ 𝔞 : FractionalIdeal (𝓞 F)⁰ F, 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  have hfin : ∀ᶠ v in Filter.cofinite, count F v (spanSingleton (𝓞 F)⁰ μ) / p = 0 := by
    filter_upwards [finite_factors (spanSingleton (𝓞 F)⁰ μ)] with v hv
    rw [hv, Int.zero_ediv]
  let exps : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
    Finsupp.ofSupportFinite (fun v ↦ count F v (spanSingleton (𝓞 F)⁰ μ) / p) hfin
  refine ⟨Finsupp.prod exps fun v z ↦ v.asIdeal ^ z,
    (eq_iff_count_eq _ ?_ (by simp [hμ₀])).mpr fun v ↦ ?_⟩
  · exact pow_ne_zero p <| Finsupp.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero (exps v)
      <| coeIdeal_ne_zero.mpr v.ne_bot
  · simp only [count_pow, count_finsuppProd]
    exact Int.mul_ediv_cancel' <| kw_mu_val_p hrF hIrr hp' v hLRam

/-- If `𝔞 ^ p = (μ)` for a fractional ideal `𝔞`, then `𝔞` is principal. -/
lemma kw_class_trivial {𝔞 : FractionalIdeal (𝓞 F)⁰ F} (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    ∃ β : F, 𝔞 = spanSingleton (𝓞 F)⁰ β := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  have h𝔞₀ : 𝔞 ≠ 0 := by
    rwa [← pow_ne_zero_iff hp.out.ne_zero, h𝔞, ne_eq, map_eq_zero]
  rw [← isPrincipal_iff, ← Units.val_mk0 h𝔞₀, ← ClassGroup.mk_eq_one_iff]
  let C := (ClassGroup.mk F) (Units.mk0 𝔞 h𝔞₀)
  have hC : C ^ p = 1 := by
    rw [← map_pow, ClassGroup.mk_eq_one_iff, Units.val_pow_eq_pow_val, Units.val_mk0, h𝔞]
    exact ⟨μ, rfl⟩
  have h₁ {a : (ZMod p)ˣ} : (Rat.galEquivZMod p F).symm a • C = C ^ a.val.val := by
    obtain ⟨c, hc₀, hc⟩ := kw_abelian_kummer hrF hIrr ((Rat.galEquivZMod p F).symm a)
    rw [ClassGroup.smul_mk', ← map_pow, eq_comm, ClassGroup.mk_eq_mk']
    refine ⟨Units.mk0 c hc₀, ?_⟩
    rw [Units.ext_iff, Units.val_mul, Units.coe_smul, Units.val_mk0, coe_toPrincipalIdeal,
      Units.val_mk0, Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_left_inj hp.out.ne_zero,
      mul_pow, ← smul_pow', pow_right_comm, h𝔞, spanSingleton_smul, AlgEquiv.smul_def, hc,
      MulEquiv.apply_symm_apply, map_mul, map_pow, map_pow, mul_comm]
  have h₂ {a b : (ZMod p)ˣ} : C ^ (a.val.val * b.val.val) = C ^ (a * b).val.val := by
    rw [Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hC]
  have h_main := stickelberger_theorem F p C
  simp_rw [← map_inv, h₁, ← pow_mul, h₂, inv_mul_cancel, Units.val_one, ZMod.val_one,
    pow_one, Finset.prod_const, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime hp.out] at h_main
  rwa [← pow_sub_one_mul hp.out.ne_zero, h_main, one_mul] at hC

open IsCMField in
/-- If `𝔞 ^ p = (μ)`, then `μ = β ^ p * η` for a unit `η` such that `η * conj η` is a `p`-th
power. -/
theorem kw_unit_conj_pow [IsCMField F] {𝔞 : FractionalIdeal (𝓞 F)⁰ F}
    (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    ∃ (β w : F) (η : (𝓞 F)ˣ), μ = β ^ p * (η : 𝓞 F) ∧
      ((η : 𝓞 F) : F) * complexConj F ((η : 𝓞 F) : F) = w ^ p := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  obtain ⟨c, hc⟩ : ∃ c, c ^ p = complexConj F μ * μ⁻¹ ^ (p - 1) := by
    obtain ⟨c, hc₁, hc₂⟩ := kw_abelian_kummer hrF hIrr (IsCMField.ratComplexConj F)
    refine ⟨c, ?_⟩
    rw [Rat.galEquivZMod_ratComplexConj, IsCMField.ratComplexConj_apply] at hc₂
    rw [hc₂, mul_assoc, left_eq_mul₀ (pow_ne_zero p hc₁), inv_pow,
      mul_inv_eq_one₀ (pow_ne_zero (p - 1) hμ₀), Units.val_neg, Units.val_one,
      ZMod.val_neg_of_ne_zero, ZMod.val_one]
  obtain ⟨β, hβ⟩ := kw_class_trivial hrF hIrr h𝔞
  rw [← pow_left_inj hp.out.ne_zero, ← map_pow] at hβ
  obtain ⟨η, hη⟩ := spanSingleton_eq_spanSingleton.mp <| hβ.symm.trans h𝔞
  rw [Units.smul_def, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] at hη
  refine ⟨β, c * μ * (β * complexConj F β)⁻¹, η, by rwa [mul_comm, eq_comm], ?_⟩
  have : β ≠ 0 := fun h ↦ hμ₀ <| by rw [← hη, h, zero_pow hp.out.ne_zero, mul_zero]
  have : complexConj F β ≠ 0 := by rwa [_root_.map_ne_zero]
  simp only [mul_pow, hc, ← hη, mul_inv, map_mul, map_pow, mul_pow, inv_pow]
  field_simp
  rw [← pow_succ', mul_assoc, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]

/-- If `𝔞 ^ p = (μ)` for a fractional ideal `𝔞`, then `L` is the cyclotomic extension
`ℚ(ζ_{p²})`. -/
lemma kw_unit_root_of_unity (hp' : Odd p) {𝔞 : FractionalIdeal (𝓞 F)⁰ F}
    (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  have : IsCMField F := Rat.isCMField F ⟨p, Set.mem_singleton p, hp.out.odd_iff.mp hp'⟩
  obtain ⟨β, w, η, hμ, hη⟩ := kw_unit_conj_pow hrF hIrr h𝔞
  obtain ⟨ζ, δ, hζ, hη'⟩ := kw_unit_eq_mul_pow hp' hη
  have hμ₁ : μ = ζ * (β * δ) ^ p := by
    rw [hμ, hη']
    ring
  have hζ₁ : ζ ≠ 1 := fun h ↦ by
    rw [h, one_mul] at hμ₁
    exact pow_ne_of_irreducible_X_pow_sub_C hIrr dvd_rfl hp.out.ne_one (β * δ) hμ₁.symm
  let α := rootOfSplitsXPowSubC hp.out.pos μ L
  let ξ : L := α * algebraMap F L (β * δ)⁻¹
  have hξ : ξ ^ p = algebraMap F L ζ := by
    rw [mul_pow, rootOfSplitsXPowSubC_pow, hμ₁, ← map_pow, ← map_mul, mul_assoc, ← mul_pow,
      mul_inv_cancel₀, one_pow, mul_one]
    exact fun h ↦ hμ₀ <| by rwa [h, zero_pow hp.out.ne_zero, mul_zero] at hμ₁
  have h₁ : orderOf ξ = p ^ 2 := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rwa [pow_one, hξ, FaithfulSMul.algebraMap_eq_one_iff]
    · rw [pow_add, pow_one, pow_mul, hξ, ← map_pow, hζ, map_one]
  have h₂ : IsCyclotomicExtension {p ^ 2} ℚ ℚ⟮ξ⟯ :=
    (IsPrimitiveRoot.iff_orderOf.mpr h₁).intermediateField_adjoin_isCyclotomicExtension ℚ
  have h₃ : ℚ ⟮ξ⟯ = ⊤ := by
    refine eq_of_le_of_finrank_eq le_top ?_
    rw [Rat.finrank (p ^ 2) ℚ⟮ξ⟯, Nat.totient_prime_pow hp.out Nat.two_pos, Nat.succ_sub_one,
      pow_one, finrank_top', ← finrank_mul_finrank ℚ F L, Rat.finrank p, Nat.totient_prime hp.out,
      hrF, mul_comm]
  rw [h₃] at h₂
  exact IsCyclotomicExtension.equiv _ _ _ topEquiv

end

end

section

/-- Two cyclic `p`-extensions `K₁`, `K₂` of `ℚ` inside a common ambient `A`, whose compositum
`K₁ ⊔ K₂` is cyclic over `ℚ`, are comparable (`K₁ ≤ K₂`) once `[K₁:ℚ] ∣ [K₂:ℚ]`. -/
lemma kw_cyclic_compositum {A : Type*} [Field A] [CharZero A] (K₁ K₂ : IntermediateField ℚ A)
    [NumberField ↑(K₁ ⊔ K₂)] [IsGalois ℚ ↑(K₁ ⊔ K₂)] [IsCyclic Gal(↑(K₁ ⊔ K₂)/ℚ)]
    (h : finrank ℚ K₁ ∣ finrank ℚ K₂) : K₁ ≤ K₂ := by
  let L := K₁ ⊔ K₂
  let K₁' := restrict (le_sup_left : K₁ ≤ L)
  let K₂' := restrict (le_sup_right : K₂ ≤ L)
  suffices K₁' ≤ K₂' from (restrict_le_restrict_iff  _ _).mp this
  rwa [← IsGalois.fixingSubgroup_le_fixingSubgroup_iff, IsCyclic.subgroup_le_iff_index_dvd,
    ← finrank_eq_fixingSubgroup_index, ← finrank_eq_fixingSubgroup_index, finrank_restrict,
    finrank_restrict]

omit hp in
/-- Let `C/ℚ` be abelian and unramified outside `p`, and `H` a subgroup of `Gal(C/ℚ)` of index `pᵐ`
with cyclic quotient. Then the fixed field of `H`, seen in `A`, is a cyclic extension of `ℚ` of
degree `pᵐ`, unramified outside `p`. -/
lemma fixedField_spec_of_index_eq_prime_pow {A : Type*} [Field A] [CharZero A]
    (C : IntermediateField ℚ A) [NumberField C] [IsAbelianGalois ℚ C]
    (hCram : UnramifiedOutside C p) {m : ℕ} (H : Subgroup Gal(C/ℚ))
    (hindex : H.index = p ^ m) (hcyc : IsCyclic (Gal(C/ℚ) ⧸ H)) :
    finrank ℚ (lift (fixedField H)) = p ^ m ∧ IsGalois ℚ (lift (fixedField H)) ∧
      IsCyclic Gal(lift (fixedField H)/ℚ) ∧ UnramifiedOutside (lift (fixedField H)) p := by
  let F := fixedField H
  refine ⟨?_, IsGalois.of_algEquiv (liftAlgEquiv _), ?_, ?_⟩
  · rwa [finrank_lift, finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  · have : IsGaloisGroup H F C := IsGaloisGroup.of_fixedPoints_eq _ ℚ _ H F rfl
    rwa [(AlgEquiv.autCongr (liftAlgEquiv _)).symm.isCyclic,
      (IsGaloisGroup.quotientMulEquiv Gal(C/ℚ) Gal(F/ℚ) ℚ F C H).symm.isCyclic ]
  · have : NumberField (lift F) := {
      to_charZero := IntermediateField.charZero (lift F),
      to_finiteDimensional := finiteDimensional_lift }
    let : Algebra (lift F) C := (inclusion (lift_le _)).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot p hCram

/-
Proof of `kw_eq_of_unique_prime_subfield`.

Let `L = K ⊔ K'`. It is abelian over `ℚ` (compositum of abelian extensions), unramified outside `p`
(`unramifiedOutside_sup'`), and its degree divides `p²ᵐ` (`finrank_sup_dvd_mul_of_isGalois`), so
`Gal(L/ℚ)` is an abelian `p`-group.
1. A subgroup of index `p` of `Gal(L/ℚ)` is the fixing subgroup of its fixed field `F`, a subfield
   of `L` of degree `p` (`finrank_eq_fixingSubgroup_index`, `fixingSubgroup_fixedField`). The field
   `F` is Galois over `ℚ` (`L/ℚ` is abelian), cyclic (prime degree) and unramified outside `p`
   (`UnramifiedOutside.tower_bot`). By `huniq`, two subgroups of index `p` have the same fixed
   field, hence are equal.
2. So `Gal(L/ℚ)` is cyclic (`IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime`).
3. The fields `K` and `K'` have the same degree, so `K ≤ K'` and `K' ≤ K` (`kw_cyclic_compositum`).
-/

/-- Two abelian extensions `K₁`, `K₂` of `ℚ` of the same degree `pᵐ`, both unramified outside `p`,
are equal if the compositum `K₁ ⊔ K₂` has only one subfield of degree `p`. (The hypothesis `huniq`
asks this only for cyclic subfields unramified outside `p`, which all degree `p` subfields of
`K₁ ⊔ K₂` are.) -/
lemma kw_eq_of_unique_prime_subfield {A : Type*} [Field A] [CharZero A]
    (K₁ K₂ : IntermediateField ℚ A) [NumberField K₁] [IsAbelianGalois ℚ K₁]
    [NumberField K₂] [IsAbelianGalois ℚ K₂] {m : ℕ}
    (hK₁ : finrank ℚ K₁ = p ^ m) (hK₂ : finrank ℚ K₂ = p ^ m)
    (hK₁ram : UnramifiedOutside K₁ p) (hK₂ram : UnramifiedOutside K₂ p)
    (huniq : ∀ (F₁ F₂ : IntermediateField ℚ A), F₁ ≤ K₁ ⊔ K₂ → F₂ ≤ K₁ ⊔ K₂ → finrank ℚ F₁ = p →
      finrank ℚ F₂ = p → UnramifiedOutside F₁ p → UnramifiedOutside F₂ p → F₁ = F₂) :
    K₁ = K₂ := by
  let L := K₁ ⊔ K₂
  let K₁' : IntermediateField ℚ L := restrict le_sup_left
  let K₂' : IntermediateField ℚ L := restrict le_sup_right
  convert_to K₁' = K₂'
  · rw [← lift_inj, lift_restrict, lift_restrict]
  suffices IsCyclic Gal(L/ℚ) by
    rw [← IsGalois.fixingSubgroup_inj, IsCyclic.subgroup_eq_iff_index_eq,
      ← finrank_eq_fixingSubgroup_index, ← finrank_eq_fixingSubgroup_index, finrank_restrict,
      finrank_restrict, hK₁, hK₂]
  have hP : IsPGroup p Gal(L/ℚ) := by
    have := finrank_sup_dvd_mul_of_isGalois K₁ K₂
    rw [hK₁, hK₂, ← pow_add, ← IsGalois.card_aut_eq_finrank] at this
    refine isPGroup_iff_card_dvd_pow.mpr ⟨m + m, this⟩
  have hLram : UnramifiedOutside L p := unramifiedOutside_sup p K₁ K₂ hK₁ram hK₂ram
  by_contra hCL
  obtain ⟨H₁, H₂, h, Hi₁, Hi₂⟩ := (IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime hP).mp hCL
  refine h ?_
  rw [← IsGalois.fixedField_inj, ← lift_inj]
  refine huniq (lift (fixedField H₁)) (lift (fixedField H₂)) (lift_le _) (lift_le _) ?_ ?_ ?_ ?_
  · rwa [finrank_lift, finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  · rwa [finrank_lift, finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  · have : NumberField (lift (fixedField H₁)) := {
      to_charZero := IntermediateField.charZero (lift (fixedField H₁)),
      to_finiteDimensional := finiteDimensional_lift }
    let : Algebra (lift (fixedField H₁)) L := (inclusion (lift_le _)).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot p hLram
  · have : NumberField (lift (fixedField H₂)) := {
      to_charZero := IntermediateField.charZero (lift (fixedField H₂)),
      to_finiteDimensional := finiteDimensional_lift }
    let : Algebra (lift (fixedField H₂)) L := (inclusion (lift_le _)).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot p hLram

/-
Proof of `ramificationIdxIn_sup_eq_lcm`.

Pick a prime `𝔓` of `𝓞 K` above `p` (`Ideal.exists_maximal_ideal_liesOver_of_isIntegral`) and let
`I` be its inertia group in `Gal(K/ℚ)`. Its order is the ramification index of `p` in `K`
(`card_inertia_eq_ramificationIdxIn`). This index divides `[K:ℚ]` (`ramificationIdxIn_dvd_finrank`),
so it is prime to `p` and `I` is cyclic (`card_inertia_notMem_iff`, `isCyclic_inertia'`). The
subgroups `I ∩ Gal(K/E)` and `I ∩ Gal(K/F)` meet trivially, since
`Gal(K/E) ∩ Gal(K/F) = Gal(K/(E ⊔ F)) = 1` (`Subgroup.subgroupOf_inf`, `fixingSubgroup_sup`,
`fixingSubgroup_top`). In a cyclic group, the order is the lcm of the indices of two subgroups
meeting trivially (`Subgroup.lcm_index_eq_card_of_isCyclic_of_inf_eq_bot`). The index of
`I ∩ Gal(K/E)` in `I` is the ramification index of `p` in `E`, because `I ∩ Gal(K/E)` is the
inertia group of `𝔓` over `E` (`Subgroup.subgroupOfEquivComm`, `Ideal.subgroupOf_inertia`) and
ramification indices multiply in towers (`ramificationIdxIn_mul_ramificationIdxIn`); same for `F`.
-/

/-- Tame Abhyankar: for a Galois `K/ℚ`, Galois intermediate fields `E`, `F` with `E ⊔ F = ⊤`, and
a prime `p ∤ [K:ℚ]`, the ramification index of `p` in `K` is the lcm of its ramification indices in
`E` and `F`. -/
theorem ramificationIdxIn_sup_eq_lcm {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (E F : IntermediateField ℚ K) [IsGalois ℚ E] [IsGalois ℚ F] (hEF : E ⊔ F = ⊤) {p : ℕ}
    [hp : Fact p.Prime] (htame : ¬ p ∣ finrank ℚ K) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) =
      Nat.lcm ((span {(p : ℤ)}).ramificationIdxIn (𝓞 E))
        ((span {(p : ℤ)}).ramificationIdxIn (𝓞 F)) := by
  obtain ⟨𝔓, _, h𝔓⟩ : ∃ 𝔓 : Ideal (𝓞 K), 𝔓.IsMaximal ∧ 𝔓.LiesOver (span {(p : ℤ)}) :=
    exists_maximal_ideal_liesOver_of_isIntegral (span {(p : ℤ)})
  have : IsCyclic (inertia Gal(K/ℚ) 𝔓) := by
    have : FaithfulSMul Gal(K/ℚ) (𝓞 K) := IsGaloisGroup.faithful ℤ
    apply isCyclic_inertia'
    rw [card_inertia_notMem_iff, ← over_def _ (span {(p : ℤ)}), absNorm_eq_natCard,
      Int.card_ideal_quot, ← ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) _ Gal(K/ℚ)]
    contrapose htame
    exact htame.trans <| RingOfIntegers.rank K ▸ ramificationIdxIn_dvd_finrank _ _ Gal(K/ℚ)
  have : E.fixingSubgroup.subgroupOf (inertia Gal(K/ℚ) 𝔓) ⊓
      F.fixingSubgroup.subgroupOf (inertia Gal(K/ℚ) 𝔓) = ⊥ := by
    rw [← Subgroup.subgroupOf_inf, ← fixingSubgroup_sup, hEF, fixingSubgroup_top,
      Subgroup.bot_subgroupOf]
  rw [← card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) _ 𝔓 ,
    ← Subgroup.lcm_index_eq_card_of_isCyclic_of_inf_eq_bot this]
  congr
  · rw [Subgroup.index_eq_iff_card_mul_eq_card,
      Nat.card_congr (E.fixingSubgroup.subgroupOfEquivComm (inertia Gal(K/ℚ) 𝔓)).toEquiv,
      subgroupOf_inertia, card_inertia_eq_ramificationIdxIn (under (𝓞 E) 𝔓),
      card_inertia_eq_ramificationIdxIn (span {(p : ℤ)}), mul_comm,
      ramificationIdxIn_mul_ramificationIdxIn _ Gal(E/ℚ) _ Gal(K/ℚ) Gal(K/E)]
  · rw [Subgroup.index_eq_iff_card_mul_eq_card,
      Nat.card_congr (F.fixingSubgroup.subgroupOfEquivComm (inertia Gal(K/ℚ) 𝔓)).toEquiv,
      subgroupOf_inertia, card_inertia_eq_ramificationIdxIn (under (𝓞 F) 𝔓),
      card_inertia_eq_ramificationIdxIn (span {(p : ℤ)}), mul_comm,
      ramificationIdxIn_mul_ramificationIdxIn _ Gal(F/ℚ) _ Gal(K/ℚ) Gal(K/F)]

/-
Proof of `ramificationIdx_eq_of_sup_eq_top`.

Write `e_K`, `e_E`, `e_L` for the ramification indices of `q` in `K`, `E`, `L`.
1. By `ramificationIdxIn_sup_eq_lcm`, the index `e_L` is `lcm(e_K, e_E)`, and
   `e_E = q - 1` (`IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime`). The index `e_K`
   divides `q - 1` (`card_inertia_dvd_card_sub_one'`): its tameness hypothesis holds because `e_K`
   divides `[K:ℚ] = pᵐ` (`ramificationIdxIn_dvd_finrank`) and `q ≠ p`. Hence `e_L = q - 1`.
2. In the tower `ℚ ⊆ E ⊆ L`, one has `e(𝔔 ∣ q) = (q - 1) e(𝔔 ∣ E)` (`ramificationIdx_tower`), so
   `e(𝔔 ∣ E) = 1`. Conclude with `ramificationIdxIn_eq_ramificationIdx`.
-/

/-- In an abelian `L/ℚ` with `E = ℚ(ζ_q) ⊆ L` and `K ⊆ L` of degree `pᵐ` such that `K ⊔ E = ⊤`, a
tame prime `q` has ramification index `q - 1` in `L`, and the prime of `E` below a prime `𝔔 ∣ q`
of `𝓞 L` has ramification index `1` in `L`. -/
lemma ramificationIdx_eq_of_sup_eq_top {L : Type*} [Field L] [NumberField L]
    [IsAbelianGalois ℚ L] (K E : IntermediateField ℚ L) [IsGalois ℚ K] [IsGalois ℚ E]
    (htop : K ⊔ E = ⊤) {q : ℕ} [hq : Fact q.Prime] (hqp : q ≠ p) [IsCyclotomicExtension {q} ℚ E]
    {m : ℕ} (hK : finrank ℚ K = p ^ m) (htame : ¬ q ∣ finrank ℚ L) (𝔔 : Ideal (𝓞 L))
    [𝔔.IsMaximal] [h𝔔 : 𝔔.LiesOver (span {(q : ℤ)})] :
    (span {(q : ℤ)}).ramificationIdxIn (𝓞 L) = q - 1 ∧
      (under (𝓞 E) 𝔔).ramificationIdxIn (𝓞 L) = 1 := by
  suffices (span {(q : ℤ)}).ramificationIdxIn (𝓞 L) = q - 1 by
    refine ⟨this, ?_⟩
    rw [← mul_right_inj' (ramificationIdxIn_ne_zero Gal(E/ℚ) (p := span {(q : ℤ)}) (B := 𝓞 E)),
      ramificationIdxIn_mul_ramificationIdxIn _ Gal(E/ℚ) _ Gal(L/ℚ) Gal(L/E), this,
      Rat.ramificationIdxIn_eq_of_prime q, mul_one]
  have : FaithfulSMul Gal(K/ℚ) (𝓞 K) := IsGaloisGroup.faithful ℤ
  have := ramificationIdxIn_sup_eq_lcm K E htop htame (p := q)
  rwa [Rat.ramificationIdxIn_eq_of_prime q E, Nat.lcm_eq_right] at this
  rw [← card_inertia_eq_ramificationIdxIn (span {(q : ℤ)}) (under (𝓞 K) 𝔔) (G := Gal(K/ℚ))]
  have := card_inertia_dvd_card_sub_one' (G := Gal(K/ℚ)) (S := 𝓞 K) (R := ℤ) (under (𝓞 K) 𝔔) ?_
  · rwa [under_under, ← (liesOver_iff _ _).mp h𝔔, Int.card_ideal_quot] at this
  rw [card_inertia_eq_ramificationIdxIn (span {(q : ℤ)})]
  rw [← Int.cast_natCast, Int.cast_mem_ideal_iff, under_under, ← (liesOver_iff _ _).mp h𝔔,
    absNorm_eq_natCard, Int.card_ideal_quot, Int.natCast_dvd_natCast]
  refine fun h ↦ hqp ?_
  have := h.trans <| ramificationIdxIn_dvd_finrank (span {(q : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [RingOfIntegers.rank, hK] at this
  exact Nat.prime_eq_prime_of_dvd_pow hq.out hp.out this

/-
Proof of `inertia_isComplement_fixingSubgroup`.

Let `I` be the inertia group of `𝔔`. By `ramificationIdx_eq_of_sup_eq_top`, its order is `q - 1`
(`card_inertia_eq_ramificationIdxIn`), and the prime of `E` below `𝔔` is unramified in `L`.
1. One has `|I| · |Gal(L/E)| = (q - 1) [L:E] = [L:ℚ]` (`IsGalois.card_fixingSubgroup_eq_finrank`,
   `IsCyclotomicExtension.Rat.finrank`, `Nat.totient_prime`).
2. By the Galois correspondence, `I ∩ Gal(L/E) = 1` means `E ⊔ fixedField I = L`
   (`codisjoint_map_orderIso_iff`, `IsGalois.fixedField_fixingSubgroup`). The field
   `E ⊔ fixedField I` is the inertia field of `𝔔` over `E` (`inertiaField_restrictScalars`), and
   `L` has degree over it the ramification index of the prime of `E` below `𝔔`
   (`finrank_inertiaField_top`), which is `1`.
`Subgroup.isComplement'_of_card_mul_and_disjoint` concludes.
-/

/-- In an abelian `L/ℚ` with `E = ℚ(ζ_q) ⊆ L` and `K ⊆ L` of degree `pᵐ` such that `K ⊔ E = ⊤`, the
inertia group of a tame prime `𝔔 ∣ q` of `𝓞 L` is a complement of `Gal(L/E)`. -/
lemma inertia_isComplement_fixingSubgroup {L : Type*} [Field L] [NumberField L]
    [IsAbelianGalois ℚ L] (K E : IntermediateField ℚ L) [IsGalois ℚ K] [IsGalois ℚ E]
    (htop : K ⊔ E = ⊤) {q : ℕ} [hq : Fact q.Prime] (hqp : q ≠ p) [IsCyclotomicExtension {q} ℚ E]
    {m : ℕ} (hK : finrank ℚ K = p ^ m) (htame : ¬ q ∣ finrank ℚ L) (𝔔 : Ideal (𝓞 L))
    [𝔔.IsMaximal] [h𝔔 : 𝔔.LiesOver (span {(q : ℤ)})] :
    Subgroup.IsComplement' (Ideal.inertia Gal(L/ℚ) 𝔔) E.fixingSubgroup := by
  obtain ⟨_, _⟩ := ramificationIdx_eq_of_sup_eq_top K E htop hqp hK htame 𝔔
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rwa [IsGalois.card_aut_eq_finrank, ← finrank_mul_finrank ℚ E L,
      IsGalois.card_fixingSubgroup_eq_finrank, mul_left_inj' finrank_pos.ne',
      Rat.finrank q, Nat.totient_prime hq.out, card_inertia_eq_ramificationIdxIn (span {(q : ℤ)})]
  · rwa [← codisjoint_toDual_iff, codisjoint_comm,
      ← codisjoint_map_orderIso_iff IsGalois.intermediateFieldEquivSubgroup.symm,
      IsGalois.intermediateFieldEquivSubgroup_symm_apply, OrderDual.ofDual_toDual,
      IsGalois.intermediateFieldEquivSubgroup_symm_apply, OrderDual.ofDual_toDual,
      IsGalois.fixedField_fixingSubgroup, codisjoint_iff, ← inertiaField,
      ← inertiaField_restrictScalars, restrictScalars_eq_top_iff, ← finrank_eq_one_iff_eq_top,
      finrank_inertiaField_top E L 𝔔 (under (𝓞 E) 𝔔)]

/-
Proof of `kw_ramification_reduction_of_sup_eq_top`.

The prime `q` is tame in `L`, since `[L:ℚ] ∣ pᵐ (q - 1)` (`finrank_sup_dvd_mul_of_isGalois`,
`IsCyclotomicExtension.Rat.finrank`, `Nat.totient_prime`). Pick a prime `𝔔` of `L` above `q`
(`Ideal.exists_maximal_ideal_liesOver_of_isIntegral`) and let `I` be its inertia group, normal
since `L/ℚ` is abelian, and a complement of `Gal(L/E)` by `inertia_isComplement_fixingSubgroup`.
Take `F = fixedField I`. Then `F ⊔ E = ⊤` and `Gal(L/ℚ) / I ≅ Gal(L/E)`
(`IsGaloisGroup.fixedPoints_sup_eq_top_of_isComplement`). So
`Gal(F/ℚ) ≅ Gal(L/ℚ) / I ≅ Gal(L/E)` (`IsGalois.normalAutEquivQuotient`, `fixingSubgroupEquiv`),
which embeds in `Gal(K/ℚ)` by restriction since `K ⊔ E = ⊤`
(`restrictRestrictAlgEquivMapHom_injective`), hence is cyclic (`isCyclic_of_injective`). Also
`[F:ℚ] = [L:E]` (`finrank_eq_fixingSubgroup_index`, `fixingSubgroup_fixedField`) divides
`[K:ℚ] = pᵐ` (`finrank_dvd_finrank_of_isGalois_of_sup_eq_top`), so it is a power of `p`
(`Nat.dvd_prime_pow`). The field `F` is unramified at `q` (`Ideal.IsInertiaRing.isUnramifiedIn`).
A prime `q'` unramified in `K` is either `q`, or unramified in `E`
(`isUnramifiedIn_of_isCyclotomicExtension`), hence in `L` (`isUnramifiedIn_sup'`) and so in `F`.
-/

set_option backward.isDefEq.respectTransparency false in
/-- Ramification reduction inside `L = K ⊔ ℚ(ζ_q)`: there is a cyclic `F ≤ L` of `p`-power degree,
unramified at `q` and at every prime where `K` is unramified, with `F ⊔ ℚ(ζ_q) = ⊤`. -/
lemma kw_ramification_reduction_of_sup_eq_top {L : Type*} [Field L] [NumberField L]
    [IsAbelianGalois ℚ L] (K E : IntermediateField ℚ L) [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    [IsGalois ℚ E] (htop : K ⊔ E = ⊤) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [IsCyclotomicExtension {q} ℚ E] {m : ℕ} (hK : finrank ℚ K = p ^ m) :
    ∃ F : IntermediateField ℚ L, IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ (∃ k, finrank ℚ F = p ^ k) ∧
      Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)}) ∧
        (∀ q' : ℕ, q'.Prime → Algebra.IsUnramifiedIn (𝓞 K) (span {(q' : ℤ)}) →
          Algebra.IsUnramifiedIn (𝓞 F) (span {(q' : ℤ)})) ∧ F ⊔ E = ⊤ := by
  have : Fact q.Prime := ⟨hq⟩
  have htame : ¬ q ∣ finrank ℚ L := fun h ↦ by
    have := h.trans <| finrank_top' (F := ℚ) (E := L) ▸ (htop ▸ finrank_sup_dvd_mul_of_isGalois K E)
    rw [hK, Rat.finrank q, Nat.totient_prime hq] at this
    obtain h | h := hq.dvd_mul.mp this
    · exact hqp <| Nat.prime_eq_prime_of_dvd_pow hq hp.out h
    · grind [Nat.dvd_sub_self_left.mp h, hq.one_lt]
  obtain ⟨𝔔, _, _⟩ : ∃ 𝔔 : Ideal (𝓞 L), 𝔔.IsMaximal ∧ 𝔔.LiesOver (span {(q : ℤ)}) :=
    exists_maximal_ideal_liesOver_of_isIntegral (span {(q : ℤ)})
  obtain ⟨h₁, ⟨e⟩⟩ := IsGaloisGroup.fixedPoints_sup_eq_top_of_isComplement _ _ _ <|
    inertia_isComplement_fixingSubgroup K E htop hqp hK htame 𝔔
  let f := (restrictRestrictAlgEquivMapHom ℚ K E L).comp
    (((IsGalois.normalAutEquivQuotient (Ideal.inertia Gal(L/ℚ) 𝔔)).symm.trans e).trans
        (fixingSubgroupEquiv E)).toMonoidHom
  have hf : Function.Injective f := (restrictRestrictAlgEquivMapHom_injective _ _ htop).comp
    (((IsGalois.normalAutEquivQuotient (Ideal.inertia Gal(L/ℚ) 𝔔)).symm.trans e).trans
      (fixingSubgroupEquiv E)).injective
  have hdvd : finrank ℚ (fixedField (Ideal.inertia Gal(L/ℚ) 𝔔)) ∣ finrank ℚ K := by
    rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Subgroup.card_dvd_of_injective _ hf
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (hK ▸ hdvd)
  let F := fixedField (Ideal.inertia Gal(L/ℚ) 𝔔)
  have : IsGaloisGroup ((inertia Gal(L/ℚ) 𝔔)) F L := .of_fixedPoints_eq Gal(L/ℚ) ℚ L _ F rfl
  refine ⟨F, IsGalois.of_fixedField_normal_subgroup _, isCyclic_of_injective f hf, ⟨k, hk⟩, ?_,
      fun r hr hKr ↦ ?_, h₁⟩
  · exact Ideal.IsInertiaRing.isUnramifiedIn Gal(L/ℚ) 𝔔
  · have : Fact r.Prime := ⟨hr⟩
    obtain rfl | hrq := eq_or_ne q r
    · exact Ideal.IsInertiaRing.isUnramifiedIn Gal(L/ℚ) 𝔔
    · refine Algebra.IsUnramifiedIn.tower_bot <|
        isUnramifiedIn_sup' _ _ htop (by simpa using NeZero.ne _) hKr ?_
      exact isUnramifiedIn_of_isCyclotomicExtension r <|
        (Nat.prime_dvd_prime_iff_eq hr hq).not.mpr hrq.symm

/-
Proof of `kw_ramification_reduction`.

Put `E = Qζ q` and `L = K ⊔ E`, abelian over `ℚ` (`IsAbelianGalois.sup`). View `K` and `E` inside
`L` (`restrict`, `restrictAlgEquiv`), so that `K ⊔ E = ⊤`, and apply
`kw_ramification_reduction_of_sup_eq_top`. Lift the resulting field to `A` (`lift`,
`liftAlgEquiv`), transferring the properties along the isomorphism
(`Algebra.IsUnramifiedIn.of_algEquiv`, `RingOfIntegers.mapIntAlgEquiv`). Lifting `F ⊔ E = ⊤` to
`A` gives `K ⊔ Qζ q = F ⊔ Qζ q` (`lift_sup`, `lift_restrict`, `lift_top`).
-/

/-- Ramification reduction: given `K/ℚ` cyclic of degree `pᵐ` with `q ≠ p` ramified, there is a
cyclic `F/ℚ` of `p`-power degree, unramified at `q` and at every prime where `K` is unramified,
such that `K ⊔ ℚ(ζ_q) = F ⊔ ℚ(ζ_q)`. -/
lemma kw_ramification_reduction {A : Type*} [Field A] [CharZero A] (Qζ : ℕ → IntermediateField ℚ A)
    [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)] [∀ n, NumberField (Qζ n)]
    [∀ n, IsAbelianGalois ℚ (Qζ n)]
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [hCK : IsCyclic Gal(K/ℚ)]
    (hK : ∃ k, finrank ℚ K = p ^ k) (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F),
      IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ (∃ k, finrank ℚ F = p ^ k) ∧
      Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)}) ∧
      (∀ q' : ℕ, q'.Prime → Algebra.IsUnramifiedIn (𝓞 K) (span {(q' : ℤ)}) →
        Algebra.IsUnramifiedIn (𝓞 F) (span {(q' : ℤ)})) ∧ K ⊔ Qζ q = F ⊔ Qζ q := by
  let L := K ⊔ (Qζ q)
  obtain ⟨k, hK⟩ := hK
  have : IsAbelianGalois ℚ L := by
    have : IsAbelianGalois ℚ K := .of_isCyclic ℚ ↥K
    exact IsAbelianGalois.sup _ _
  let K₀ : IntermediateField ℚ L := restrict le_sup_left
  let E₀ : IntermediateField ℚ L := restrict le_sup_right
  have htop : K₀ ⊔ E₀ = ⊤ := by
    rw [← lift_inj, lift_sup, lift_restrict, lift_restrict, lift_top]
  have : IsCyclic Gal(K₀/ℚ) := (restrictAlgEquiv le_sup_left).autCongr.isCyclic.mp hCK
  have : IsCyclotomicExtension {q} ℚ E₀ := .equiv _ ℚ (Qζ q) (restrictAlgEquiv le_sup_right)
  obtain ⟨F₀, _, h₁, _, h₂, h₃, h₄⟩ := kw_ramification_reduction_of_sup_eq_top K₀ E₀ htop hq hqp
    (by rwa [finrank_restrict])
  refine ⟨lift F₀, .of_ringEquiv _ _ (liftAlgEquiv F₀).toRingEquiv, .of_algEquiv (liftAlgEquiv F₀),
    (liftAlgEquiv F₀).autCongr.isCyclic.mp h₁, by simpa [finrank_lift], ?_, fun r hr hr' ↦ ?_, ?_⟩
  · exact Algebra.IsUnramifiedIn.of_algEquiv
      (RingOfIntegers.mapIntAlgEquiv (liftAlgEquiv F₀).toRingEquiv) h₂
  · exact Algebra.IsUnramifiedIn.of_algEquiv
      (RingOfIntegers.mapIntAlgEquiv (liftAlgEquiv F₀).toRingEquiv) <|
      h₃ r hr <| Algebra.IsUnramifiedIn.of_algEquiv
      (RingOfIntegers.mapIntAlgEquiv (restrictAlgEquiv le_sup_left).toRingEquiv) hr'
  · have :=  congr_arg lift <| htop.trans h₄.symm
    rwa [lift_sup, lift_sup, lift_restrict, lift_restrict] at this

omit hp in
/-- For a family `Qζ` of cyclotomic fields, `Qζ (lcm a b) = Qζ a ⊔ Qζ b` when `a, b ≠ 0`. -/
theorem cyclotomic_lcm {A : Type*} [Field A] [CharZero A] (Qζ : ℕ → IntermediateField ℚ A)
    [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Qζ (a.lcm b) = Qζ a ⊔ Qζ b := by
  have : NeZero a := ⟨ha⟩
  have : NeZero b := ⟨hb⟩
  have := isCyclotomicExtension_lcm_sup ℚ A a b (Qζ a) (Qζ b)
  exact isCyclotomicExtension_eq {a.lcm b} ℚ A _ _

/-
Proof of `kw_reduce_to_unramified_outside_p`.

Strong induction on the number `N` of primes `q ≠ p` ramified in `K`, generalising over `K`
(`Nat.strong_induction_on`). This set is finite since its elements divide the discriminant of `K`
(`not_dvd_discr_iff_isUnramifiedIn`), which is nonzero (`discr_ne_zero`), so it is contained in the
prime factors of `discr K` (`Nat.mem_primeFactors_of_ne_zero`, `Finset.finite_toSet`). If it is
empty (`Set.eq_empty_or_nonempty`), take `F = K` and `n = 1`. Otherwise pick `r` in it.
`kw_ramification_reduction` gives `E` cyclic of `p`-power degree, unramified at `r` and at every
prime unramified in `K`, with `K ⊔ ℚ(ζ_r) = E ⊔ ℚ(ζ_r)`. So `E` has fewer ramified primes
(`Set.ncard_lt_ncard`), and the induction hypothesis gives `F` unramified outside `p` and `n ≠ 0`
with `E ⊔ ℚ(ζ_n) = F ⊔ ℚ(ζ_n)`. Since `ℚ(ζ_lcm(r, n)) = ℚ(ζ_r) ⊔ ℚ(ζ_n)` (`cyclotomic_lcm`), one
gets `K ⊔ ℚ(ζ_lcm(r, n)) = F ⊔ ℚ(ζ_lcm(r, n))` (`sup_assoc`, `sup_comm`).
-/

/-- Iterating the ramification reduction over the finitely many primes `q ≠ p` ramified in `K`,
one obtains a cyclic `F/ℚ` of `p`-power degree, unramified outside `p`, with
`K ⊔ Qζ n = F ⊔ Qζ n` for some `n ≠ 0` (so `K` is cyclotomic iff `F` is). -/
lemma kw_reduce_to_unramified_outside_p {A : Type*} [Field A] [CharZero A]
    (Qζ : ℕ → IntermediateField ℚ A)
    [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)] [∀ n, NumberField (Qζ n)]
    [∀ n, IsAbelianGalois ℚ (Qζ n)]
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (hK : ∃ k, finrank ℚ K = p ^ k) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (_ : IsGalois ℚ F) (_ : IsCyclic Gal(F/ℚ)),
      (∃ k, finrank ℚ F = p ^ k) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)})) ∧
      ∃ n, n ≠ 0 ∧ K ⊔ Qζ n = F ⊔ Qζ n := by
  have hfin (E : IntermediateField ℚ A) [NumberField E] :
      {q : ℕ | q.Prime ∧ q ≠ p ∧ ¬ Algebra.IsUnramifiedIn (𝓞 E) (span {(q : ℤ)})}.Finite := by
    refine (Nat.primeFactors (discr E).natAbs).finite_toSet.subset fun q ⟨hq, hqp, hram⟩ ↦ ?_
    rwa [SetLike.mem_coe, Nat.mem_primeFactors_of_ne_zero, and_iff_right hq,
      ← Int.natCast_dvd, ← not_not (a := (q : ℤ) ∣ discr E),
      not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) (Nat.prime_iff_prime_int.mp hq)]
    simpa using discr_ne_zero _
  induction h : {q | q.Prime ∧ q ≠ p ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})}.ncard
      using Nat.strong_induction_on generalizing K with
  | _ N h_ind =>
    obtain hS | ⟨r, hr, hrp, hrram⟩ := Set.eq_empty_or_nonempty
      {q : ℕ | q.Prime ∧ q ≠ p ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})}
    · refine ⟨K, inferInstance, inferInstance, inferInstance, hK,
          fun q hq hqp ↦ ?_, 1, one_ne_zero, rfl⟩
      contrapose! hS
      exact ⟨q, hq, hqp, hS⟩
    · obtain ⟨E, _, _, _, hE, hEr, hEram, hKE⟩ := kw_ramification_reduction Qζ K hK r hr hrp
      have hlt : {q | q.Prime ∧ q ≠ p ∧
          ¬ Algebra.IsUnramifiedIn (𝓞 E) (span {(q : ℤ)})}.ncard < N :=
        h ▸ Set.ncard_lt_ncard ⟨by grind, by aesop⟩ (hfin K)
      obtain ⟨F, _, _, _, hF, hFram, n, hn, hEF⟩ := h_ind _ hlt E hE rfl
      refine ⟨F, ‹_›, ‹_›, ‹_›, hF, hFram, r.lcm n, Nat.lcm_ne_zero hr.ne_zero hn, ?_⟩
      rw [cyclotomic_lcm Qζ hr.ne_zero hn, ← sup_assoc, hKE, sup_assoc, sup_comm (Qζ r),
        ← sup_assoc, hEF, sup_assoc]

end

section

/-- Every cyclic extension of `ℚ` of prime degree `p` (odd) unramified outside `p` is contained in
`ℚ(ζ_{p²}) = Qζ (p ^ 2)`. -/
theorem prop_kw_exponent_p (hp' : Odd p) {A : Type*} [Field A] [CharZero A]
    (Qζ : ℕ → IntermediateField ℚ A)
    [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)] [∀ n, NumberField (Qζ n)]
    [∀ n, IsAbelianGalois ℚ (Qζ n)]
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (hK : finrank ℚ K = p) (hKram : UnramifiedOutside K p) :
    K ≤ Qζ (p ^ 2) := by
  have : IsAbelianGalois ℚ K := .of_isCyclic ℚ K
  let L := K ⊔ Qζ p
  have : IsCyclotomicExtension {p ^ 2} ℚ L := by
    let : Algebra (Qζ p) L := (inclusion (le_sup_right : Qζ p ≤ L)).toRingHom.toAlgebra
    have : Module.finrank ℚ ↑(K ⊓ Qζ p) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes ?_ (finrank_dvd_of_le_right inf_le_left)
        (finrank_dvd_of_le_right inf_le_right)
      rw [hK, Rat.finrank p, Nat.totient_prime hp.out]
      exact (Nat.coprime_self_sub_right hp.out.one_le).mpr (Nat.coprime_one_right p)
    have hL : Module.finrank ℚ L = p * (p - 1) := by
      rw [IntermediateField.LinearDisjoint.finrank_sup, hK, Rat.finrank p, Nat.totient_prime hp.out]
      rwa [LinearDisjoint.iff_inf_eq_bot, ← IntermediateField.finrank_eq_one_iff]
    obtain ⟨_, _, hrF⟩ := kw_kummer₀ (Qζ p) hL
    obtain ⟨μ, hμ₀, _⟩ := kw_kummer hrF
    have hIrr : Irreducible (X ^ p - C μ) :=
      irreducible_X_pow_sub_C_of_isSplittingField (primitiveRoots_nonempty p ℚ (Qζ p)) hrF
    have hramL : UnramifiedOutside L p :=
      unramifiedOutside_sup p _ _ hKram (UnramifiedOutside.of_isCyclotomicExtension' p (Qζ p))
    obtain ⟨𝔞, h𝔞⟩ := kw_mu_pth_power_ideal hrF hIrr hp' hramL
    exact kw_unit_root_of_unity hrF hIrr hp' h𝔞
  rw [isCyclotomicExtension_eq {p ^ 2} ℚ _ (Qζ (p ^ 2)) L]
  exact le_sup_left

/-- Two cyclic extensions of `ℚ` of prime degree `p` (odd) unramified outside `p` are equal. -/
theorem prop_kw_exponent_p_eq (hp' : Odd p) {A : Type*} [Field A] [CharZero A]
    (Qζ : ℕ → IntermediateField ℚ A)
    [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)] [∀ n, NumberField (Qζ n)]
    [∀ n, IsAbelianGalois ℚ (Qζ n)]
    (K₁ K₂ : IntermediateField ℚ A) [NumberField K₁]
    [IsGalois ℚ K₁] [IsCyclic Gal(K₁/ℚ)] (hK₁ : finrank ℚ K₁ = p) (hKram₁ : UnramifiedOutside K₁ p)
    [NumberField K₂] [IsGalois ℚ K₂] [IsCyclic Gal(K₂/ℚ)] (hK₂ : finrank ℚ K₂ = p)
    (hKram₂ : UnramifiedOutside K₂ p) :
    K₁ = K₂ := by
  have h₁ := prop_kw_exponent_p hp' Qζ K₁ hK₁ hKram₁
  have h₂ := prop_kw_exponent_p hp' Qζ K₂ hK₂ hKram₂
  suffices restrict h₁ = restrict h₂ by
    rwa [← lift_inj, lift_restrict h₁, lift_restrict h₂] at this
  have : IsCyclic Gal(Qζ (p ^ 2)/ℚ) :=
    Rat.isCyclic_of_prime_pow _ 2 <| hp'.ne_two_of_dvd_nat dvd_rfl
  rw [← IsGalois.fixingSubgroup_inj, IsCyclic.subgroup_eq_iff_index_eq,
    ← finrank_eq_fixingSubgroup_index, ← finrank_eq_fixingSubgroup_index, finrank_restrict,
    finrank_restrict, hK₁, hK₂]

/-- Every cyclic extension of `ℚ` of odd prime power degree `pᵐ` unramified outside `p` is
cyclotomic: contained in `ℚ(ζ_{p^{m+1}}) = Qζ (p ^ (m + 1))` inside the ambient field `A`. -/
theorem prop_kw_odd_prime_power [Fact (Odd p)] {A : Type*} [Field A] [CharZero A]
    (Qζ : ℕ → IntermediateField ℚ A)
    [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)] [∀ n, NumberField (Qζ n)]
    [∀ n, IsAbelianGalois ℚ (Qζ n)]
    (m : ℕ) (hm : 0 < m) (K : IntermediateField ℚ A)
    [NumberField K] [IsAbelianGalois ℚ K] (hK : finrank ℚ K = p ^ m)
    (hKram : UnramifiedOutside K p) :
    K ≤ Qζ (p ^ (m + 1)) := by

  sorry

end
