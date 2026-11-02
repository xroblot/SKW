module

public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.FractionalIdeal
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.KummerExtension
public import SKW.Prereqs.OtherPR
public import SKW.Prereqs.Unramified

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion

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

variable [NumberField L] [IsAbelianGalois ℚ L] {μ : F} [hS : IsSplittingField F L (X ^ p - C μ)]
  (hIrr : Irreducible (X ^ p - C μ))

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
