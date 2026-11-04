module

public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.FractionalIdeal
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.KummerExtension
public import SKW.Prereqs.OtherPR
public import SKW.Prereqs.Unramified
public import SKW.Stickelberger.Stickelberger
public import SKW.Prereqs.CMField

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.RingTheory.ClassGroup.Basic

set_option linter.style.header false

@[expose] public section

/-!
# The Kummer step of the Kronecker-Weber theorem

Let `p` be an odd prime, `F = ℚ(ζ_p)` and `L/F` a cyclic extension of degree `p`, with `L/ℚ`
abelian.

This file establishes
- `kw_kummer₀`: if `L/ℚ` is Galois of degree `p * (p - 1)`, then `L/F` is cyclic of degree `p`.
- `kw_kummer`: `L/F` is a Kummer extension `F(ᵖ√μ)` for some nonzero `μ ∈ F`.
- `kw_abelian_kummer`: the Kummer criterion for `L/ℚ` to be abelian.
- `kw_split_prime`: if `p ∤ v(μ)`, then the stabilizer of `v` in `Gal(F/ℚ)` is trivial.
- `kw_mu_val_p`: if `L/F` is unramified outside `p`, then `p ∣ v(μ)` for every prime `v` of `F`.
- `kw_mu_pth_power_ideal`: if `L/F` is unramified outside `p`, then `(μ) = 𝔞 ^ p` for some
  fractional ideal `𝔞` of `F`.
-/

open NumberField Ideal Polynomial Pointwise IntermediateField Module IsCyclotomicExtension
  nonZeroDivisors IsDedekindDomain FractionalIdeal

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

section

variable {F L : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F] [Field L]
  [NumberField L] [Algebra F L] [IsGalois ℚ L]

/-- If `L/ℚ` is Galois of degree `p * (p - 1)`, then `L/F` is cyclic Galois of degree `p`. -/
lemma kw_kummer₀ (hL : Module.finrank ℚ L = p * (p - 1)) :
    IsGalois F L ∧ IsCyclic Gal(L/F) ∧ finrank F L = p := by
  have hF : finrank ℚ F = p - 1 := Nat.totient_prime hp.out ▸ IsCyclotomicExtension.Rat.finrank p F
  have hrF : finrank F L = p := by
    have h := Module.finrank_mul_finrank ℚ F L
    rw [hF, hL, mul_comm p (p - 1)] at h
    exact Nat.eq_of_mul_eq_mul_left (by have := hp.out.one_lt; omega) h
  have : IsGalois F L := IsGalois.tower_top_of_isGalois ℚ F L
  exact ⟨this, isCyclic_of_prime_card <| by rw [IsGalois.card_aut_eq_finrank, hrF], hrF⟩

end

variable (F : Type*) [Field F] [NumberField F] {L : Type*} [Field L] [Algebra F L]

section

variable [NumberField L] {μ : F} [IsSplittingField F L (X ^ p - C μ)]

/-- If `L` is unramified outside `p` and `v` is a prime of `𝓞 F` above a prime `q ≠ p`, then
`p ∣ v(μ)`. -/
lemma kw_mu_val_p_of_liesOver_ne {v : HeightOneSpectrum (𝓞 F)} {q : ℕ} [hq : Fact q.Prime]
    [v.asIdeal.LiesOver (span {(q : ℤ)})] (hqp : q ≠ p) (hLRam : UnramifiedOutside L p) :
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

variable [IsCyclotomicExtension {p} ℚ F] [FiniteDimensional F L] [IsGalois F L]
  [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p)

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

variable [NumberField L] [IsAbelianGalois ℚ L] {μ : F} [hS : IsSplittingField F L (X ^ p - C μ)]
  (hIrr : Irreducible (X ^ p - C μ))

open IsCMField in
/-- If `η * conj η` is a `p`-th power, then `η = ξ * δ ^ p` with `ξ ^ p = 1`. -/
lemma kw_unit_eq_mul_pow [IsCMField F] (hp' : Odd p) {η : (𝓞 F)ˣ} {w : F}
    (hη : (η.val : F) * complexConj F (η.val : F) = w ^ p) :
    ∃ ξ δ : F, ξ ^ p = 1 ∧ ((η : 𝓞 F) : F) = ξ * δ ^ p := by
  obtain ⟨ζ, ε, hε, h⟩ := exists_torsion_realunits_pow_indexRealUnits_eq_mul η
  rw [Rat.indexRealUnits_eq_one' p _ (by grind), pow_one] at h
  have ⟨γ, hγ⟩ : ∃ γ : F, ε = γ ^ p := by
    have : η.val * (complexConj F) η.val = ε.val ^ 2 := by
      rw [← coe_ringOfIntegersComplexConj, ← coe_unitsComplexConj, ← Units.coe_mul, ← Units.coe_pow,
        RingOfIntegers.eq_iff, ← Units.ext_iff, h, map_mul, unitsComplexConj_torsion,
        (unitsComplexConj_eq_self_iff _ ε).mpr hε, Subgroup.coe_inv, mul_mul_mul_comm,
        mul_inv_cancel, one_mul, sq]
    refine ⟨w ^ Nat.gcdA 2 p * ε ^ Nat.gcdB 2 p, ?_⟩
    rw [mul_pow, ← zpow_natCast, zpow_comm, zpow_natCast, ← hη, this, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul', ← zpow_add₀ ε.coe_ne_zero, ← Nat.gcd_eq_gcd_ab,
      Nat.coprime_two_left.mpr hp', Nat.cast_one, zpow_one]
  have hζ : (ζ.val : F) ^ (2 * p) = 1 := by
    rw [show 2 * p = Nat.card (Units.torsion F) by
      rw [← Units.torsionOrder, IsCyclotomicExtension.Rat.torsionOrder_eq (n := p),
        ite_eq_right (Nat.not_even_iff_odd.mpr hp')], ← map_pow, ← Units.val_pow_eq_pow_val,
        ← SubmonoidClass.coe_pow, pow_card_eq_one', Subgroup.coe_one, Units.val_one, map_one]
  refine ⟨(ζ.val : F) ^ (p + 1), ζ.val * γ, ?_, ?_⟩
  · have h : (p + 1) * p = (2 * p) * ((p + 1) / 2) := by
      rw [mul_comm 2, mul_assoc, Nat.mul_div_eq_iff_dvd.mpr, mul_comm]
      grind
    rw [← pow_mul, h, pow_mul, hζ, one_pow]
  · rw [mul_pow, ← mul_assoc, ← pow_add, show p + 1 + p = 2 * p + 1 by ring, pow_add, hζ, one_mul,
      pow_one, ← hγ, ← map_mul, ← Units.val_mul, ← h]

include hIrr hrF

/-- The Kummer criterion for `L/ℚ` to be abelian: every `σ ∈ Gal(F/ℚ)` sends `μ` to
`c ^ p * μ ^ a`, where `a` is the image of `σ` in `(ℤ/pℤ)ˣ`. -/
theorem kw_abelian_kummer (σ : Gal(F/ℚ)) :
    ∃ c : F, c ≠ 0 ∧ σ μ = c ^ p * μ ^ (Rat.galEquivZMod p F σ).val.val := by
  have hne : (primitiveRoots p F).Nonempty := primitiveRoots_nonempty p ℚ F
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  obtain ⟨τ, hτ⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hCF
  set a := rootOfSplitsXPowSubC hp.out.pos μ L with a_def
  have hμ : algebraMap F L μ = a ^ p  := (rootOfSplitsXPowSubC_pow _ _).symm
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
    rw [← IsCyclotomicExtension.Rat.apply_eq_pow_iff_galEquivZMod_eq hζ]
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
  obtain ⟨c, hc₀, hc₁⟩ := kw_abelian_kummer p F hrF hIrr σ
  have : count F v (spanSingleton (𝓞 F)⁰ μ) = count F v (spanSingleton (𝓞 F)⁰ (σ μ)) := by
    rw [← AlgEquiv.smul_def, ← spanSingleton_smul]
    have := FractionalIdeal.count_smul F v ((spanSingleton (𝓞 F)⁰) μ) σ
    rw [← FractionalIdeal.count_smul _ _ _ σ, hσ]
  have := congr_arg (· : ℤ → ZMod p) this
  rwa [hc₁, map_mul, map_pow, map_pow, count_mul _ _ (by simp [hc₀]) (by simp [hμ₀]), count_pow,
    count_pow, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
    Int.cast_mul, right_eq_mul₀, Int.cast_natCast, ZMod.natCast_zmod_val] at this
  rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If `v` is a prime of `𝓞 F` above `p`, then `p ∣ v(μ)`. -/
lemma kw_mu_val_p_of_liesOver {v : HeightOneSpectrum (𝓞 F)}
    [v.asIdeal.LiesOver (span {(p : ℤ)})] (hp' : Odd p) :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  have : IsGalois ℚ F := isGalois {p} ℚ F
  have : Nontrivial (MulAction.stabilizer Gal(F/ℚ) v.asIdeal) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [Ideal.card_stabilizer_eq (span {(p : ℤ)}), Rat.ramificationIdxIn_eq_of_prime,
      Rat.inertiaDegIn_eq_of_prime, mul_one]
    lia [hp.out.odd_iff.mp hp']
  obtain ⟨σ, hσ⟩ := exists_ne (1 : MulAction.stabilizer Gal(F/ℚ) v.asIdeal)
  by_contra hv
  refine hσ <| Subtype.ext <| kw_split_prime p F hrF hIrr hv ?_
  rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.smul_asIdeal, σ.prop]

/-- If `L` is unramified outside `p`, then `p ∣ v(μ)` for every prime `v` of `𝓞 F`. -/
lemma kw_mu_val_p (v : HeightOneSpectrum (𝓞 F)) (hLRam : UnramifiedOutside L p) (hp' : Odd p) :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  have : Fact (absNorm (under ℤ v.asIdeal)).Prime := ⟨Nat.absNorm_under_prime v.asIdeal⟩
  have hv : v.asIdeal.LiesOver (span {((absNorm (under ℤ v.asIdeal) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm v.asIdeal
  by_cases hqp : absNorm (under ℤ v.asIdeal) = p
  · rw [hqp] at hv
    exact kw_mu_val_p_of_liesOver p F hrF hIrr hp'
  · exact kw_mu_val_p_of_liesOver_ne p F hqp hLRam

/-- If `L` is unramified outside `p`, then `(μ) = 𝔞 ^ p` for a fractional ideal `𝔞` of `F`. -/
lemma kw_mu_pth_power_ideal (hLram : UnramifiedOutside L p) (hp' : Odd p) :
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
    exact Int.mul_ediv_cancel' <| kw_mu_val_p p F hrF hIrr v hLram hp'

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
    obtain ⟨c, hc₀, hc⟩ := kw_abelian_kummer p F hrF hIrr ((Rat.galEquivZMod p F).symm a)
    rw [ClassGroup.smul_mk', ← map_pow, eq_comm, ClassGroup.mk_eq_mk']
    refine ⟨Units.mk0 c hc₀, ?_⟩
    rw [Units.ext_iff, Units.val_mul, Units.coe_smul, Units.val_mk0, coe_toPrincipalIdeal,
      Units.val_mk0, Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_left_inj hp.out.ne_zero,
      mul_pow, ← smul_pow', pow_right_comm, h𝔞, spanSingleton_smul, AlgEquiv.smul_def, hc,
      MulEquiv.apply_symm_apply, map_mul, map_pow, map_pow, mul_comm]
  have h₂ {a b : (ZMod p)ˣ} : C ^ (a.val.val * b.val.val) = C  ^ (a * b).val.val := by
    rw [Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hC]
  have h_main := stickelberger_theorem F p C
  simp_rw [← map_inv, h₁, ← pow_mul, h₂, inv_mul_cancel, Units.val_one, ZMod.val_one,
    pow_one, Finset.prod_const, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime hp.out] at h_main
  rwa [← pow_sub_one_mul hp.out.ne_zero, h_main, one_mul] at hC

-- 1. The ideal 𝔞 is principal (Stickelberger).
--   - Action of σ_a on the class of 𝔞. By kw_abelian_kummer, σ_a(μ) = c ^ p · μ ^ a for
--      some c ∈ Fˣ. Applying σ_a to 𝔞 ^ p = (μ) gives (σ_a 𝔞) ^ p = (c) ^ p · (𝔞 ^ a) ^ p.
--   - The group of nonzero fractional ideals is torsion-free (it is free abelian on the primes),
--      so σ_a 𝔞 = (c) · 𝔞 ^ a. Hence [σ_a 𝔞] = [𝔞] ^ a in Cl(F).
--   - Applying Stickelberger. The class [𝔞] is killed by p, because [𝔞] ^ p = [(μ)] = 1.
--      Stickelberger's theorem says θ = Σ_a a · σ_a⁻¹ kills Cl(F), so
--      1 = ∏_a (σ_a⁻¹ [𝔞]) ^ a = ∏_a [𝔞] ^ (a⁻¹ · a) = [𝔞] ^ (p - 1).
--   - Conclusion. Together with [𝔞] ^ p = 1, this gives [𝔞] = 1, so 𝔞 = (β) with β ∈ Fˣ.

open IsCMField in
/-- If `𝔞 ^ p = (μ)`, then `μ = β ^ p * η` for a unit `η` such that
  `η * conj η` is a `p`-th power. -/
theorem kw_unit_conj_pow [IsCMField F] {𝔞 : FractionalIdeal (𝓞 F)⁰ F}
    (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    ∃ (β w : F) (η : (𝓞 F)ˣ), μ = β ^ p * (η : 𝓞 F) ∧
      ((η : 𝓞 F) : F) * complexConj F ((η : 𝓞 F) : F) = w ^ p := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  obtain ⟨c, hc⟩ : ∃ c, c ^ p = complexConj F μ * μ⁻¹ ^ (p - 1) := by
    obtain ⟨c, hc₁, hc₂⟩ := kw_abelian_kummer p F hrF hIrr (IsCMField.ratComplexConj F)
    refine ⟨c, ?_⟩
    rw [Rat.galEquivZMod_ratComplexConj, IsCMField.ratComplexConj_apply] at hc₂
    rw [hc₂, mul_assoc, left_eq_mul₀ (pow_ne_zero p hc₁), inv_pow,
      mul_inv_eq_one₀ (pow_ne_zero (p - 1) hμ₀), Units.val_neg, Units.val_one,
      ZMod.val_neg_of_ne_zero, ZMod.val_one]
  obtain ⟨β, hβ⟩ := kw_class_trivial p F hrF hIrr h𝔞
  rw [← pow_left_inj hp.out.ne_zero, ← map_pow] at hβ
  obtain ⟨η, hη⟩ := spanSingleton_eq_spanSingleton.mp <| hβ.symm.trans h𝔞
  rw [Units.smul_def, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] at hη
  refine ⟨β, c * μ * (β * complexConj F β)⁻¹, η, by rwa [mul_comm, eq_comm], ?_⟩
  have : β ≠ 0 := fun h ↦ hμ₀ <| by rw [← hη, h, zero_pow hp.out.ne_zero, mul_zero]
  have : complexConj F β ≠ 0 := by rwa [_root_.map_ne_zero]
  simp only [mul_pow, hc, ← hη, mul_inv, map_mul, map_pow, mul_pow, inv_pow]
  field_simp
  rw [← pow_succ', mul_assoc, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]

--   2. A unit appears. From (β) ^ p = (μ) we get (μ / β ^ p) = (1), so
--      μ = β ^ p · η with η ∈ (𝓞 F)ˣ. With μ ∈ F this is simpler than in the old
--      proof: there is no integral α and no 𝔞 ≠ 0 to carry.

--   3. Complex conjugation. Take σ = σ_{-1}, which is complex conjugation on F.
--      Kummer gives σ(μ) = c ^ p · μ ^ (p - 1), so μ · σ(μ) is a p-th power, and hence
--      η · σ(η) = w ^ p for some w ∈ F.

--   4. Units of the CM field F. The field F is CM since p is odd.
--   - The index of the real units of F is 1, so η = ζ' · ε with ζ' a root of unity and ε a
--      real unit.
--   - Then η · σ(η) = ε ^ 2 = w ^ p. Since gcd(2, p) = 1, it follows that ε = γ ^ p for some γ ∈ F.
--   - The torsion of F has order 2p, so η = ζ · δ ^ p with ζ = ζ' ^ (p + 1), ζ ^ p = 1 and
--      δ = ζ' · γ.

/-- If `𝔞 ^ p = (μ)` for a fractional ideal `𝔞`, then `L` is the cyclotomic extension
`ℚ(ζ_{p²})`. -/
lemma kw_unit_root_of_unity (hp' : Odd p) {𝔞 : FractionalIdeal (𝓞 F)⁰ F}
    (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  have : IsCMField F := Rat.isCMField F ⟨p, Set.mem_singleton p, hp.out.odd_iff.mp hp'⟩
  obtain ⟨β, w, η, hμ, hη⟩ := kw_unit_conj_pow p F hrF hIrr h𝔞
  obtain ⟨ζ, δ, hζ, hη'⟩ := kw_unit_eq_mul_pow p F hp' hη
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
