module

public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.KummerExtension
public import SKW.Prereqs.OtherPR
public import SKW.Prereqs.Unramified

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion

set_option linter.style.header false

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

/-
╔══════════════════════════════════════════════════════════════════════════════════════════════╗
║ TODO(SKW), PLANNED REFACTOR (29 October 2026): take `μ ∈ Fˣ` instead of `μ : 𝓞 F`, here and in ║
║ `ClassGroup.lean`. Full write-up: item 6 of "Reste à faire" in                               ║
║ `~/Desktop/Claude/Lean/KroneckerWeber/plan_kronecker_weber.md`.                              ║
╚══════════════════════════════════════════════════════════════════════════════════════════════╝

The integrality of `μ` is only used to stay inside `Ideal (𝓞 F)`. The plan:
* `kw_kummer`, `kw_abelian_kummer`: field statements; with
  `exists_root_adjoin_eq_top_of_isCyclic'` the element `x` works as is, no
  `exists_integer_multiple`.
* `kw_split_prime`: `hv` is only used to cancel `v_𝔮(μ)` modulo `p`, all valuations are taken in
  `F`; rewrite with `FractionalIdeal.count` (no `d ^ p`, no `FiniteMultiplicity` goals). The
  `have h₃` there is dead.
* `kw_mu_val_p`: the case `q = p` only uses `kw_split_prime`. The case `q ≠ p` is the only place
  taking a valuation in `L`; apply the current integral argument to `d ^ p * μ` (same `v_𝔮`
  modulo `p`, same `L`, root `d * α`), so no "count of an extended fractional ideal" API needed.
* `kw_mu_pth_power_ideal`: `𝔞 := ∏ᶠ v, v ^ (count v (μ) / p)` as a fractional ideal.
* `kw_class_trivial`: apply Stickelberger to the class of the fractional ideal `𝔞`.
* `exists_pth_root` goes away.
-/

open NumberField Ideal Polynomial Pointwise IntermediateField Module IsCyclotomicExtension
  nonZeroDivisors

noncomputable section IsScalarTower

variable (p : ℕ) [hp : Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]
variable {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L]
  [IsGalois F L] [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p)

include hrF in
/-- The extension `L/F` is a Kummer extension: `L` is the splitting field of `X ^ p - μ` for some
nonzero `μ ∈ 𝓞 F`. -/
lemma kw_kummer :
    ∃ μ : 𝓞 F, μ ≠ 0 ∧
      IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ)) := by
  have hne : (primitiveRoots (Module.finrank F L) F).Nonempty :=
    hrF ▸ primitiveRoots_nonempty p ℚ F
  obtain ⟨g, hg, ⟨x, hx₁⟩, hx₂⟩ := exists_root_adjoin_eq_top_of_isCyclic' F L hne
  have hx₀ : x ≠ 0 :=
      fun h ↦ hg <| by rwa [h, map_zero, eq_comm, pow_eq_zero_iff finrank_pos.ne'] at hx₁
  obtain ⟨d, hd₁, ⟨μ, hμ⟩⟩ := exists_integer_multiple x
  have hμ₀ : μ ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mp <| hμ ▸ mul_ne_zero_iff.mpr ⟨Int.cast_ne_zero.mpr hd₁, hx₀⟩
  refine ⟨d ^ (finrank F L - 1) * μ, mul_ne_zero (by aesop) hμ₀, ?_⟩
  · have : F⟮d * g⟯ = ⊤ := by
      rw [mul_comm, ← map_intCast (algebraMap F L),
        adjoin_simple_mul_algebraMap _ _ (Int.cast_ne_zero.mpr hd₁), hx₂]
    refine hrF ▸ isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hne ?_ this
    simp_rw [map_mul, hμ, map_mul, map_pow, map_intCast, ← mul_assoc, ← pow_succ, hx₁,
      Nat.sub_add_cancel finrank_pos, mul_pow]

variable [NumberField L] [IsAbelianGalois ℚ L]

variable {μ : 𝓞 F} (hμ : μ ≠ 0)
  [hS : IsSplittingField F L (X ^ p - C (algebraMap (𝓞 F) F μ))]
  (hIrr : Irreducible (X ^ p - C ((algebraMap (𝓞 F) F) μ)))

omit hCF [IsGalois F L] [IsAbelianGalois ℚ L] [NumberField L] [FiniteDimensional F L] in
include hrF hIrr in
/-- The element `μ` has a nonzero `p`-th root in `𝓞 L`. -/
lemma exists_pth_root :
    ∃ (α : 𝓞 L), α ≠ 0 ∧ algebraMap (𝓞 F) (𝓞 L) μ = α ^ p := by
  have hF : (primitiveRoots p F).Nonempty := primitiveRoots_nonempty p ℚ F
  have hβ := rootOfSplitsXPowSubC_pow (n := p) (algebraMap (𝓞 F) F μ) L
  obtain ⟨α, hα⟩ : ∃ α : 𝓞 L, (rootOfSplitsXPowSubC (NeZero.pos p) (μ : F) L) =
      algebraMap (𝓞 L) L α := by
    refine ⟨⟨rootOfSplitsXPowSubC (NeZero.pos p) (μ : F) L, ?_⟩, rfl⟩
    rw [mem_integralClosure_iff, ← IsIntegral.pow_iff (NeZero.pos p)]
    rw [hβ, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap_iff.mpr <| RingOfIntegers.isIntegral μ
  refine ⟨α, ?_, ?_⟩
  · have := adjoin_root_eq_top_of_isSplittingField hF hIrr hβ
    contrapose! this
    rw [hα, this, map_zero, adjoin_zero, Ne.eq_def, bot_eq_top_iff_finrank_eq_one, hrF]
    exact hp.out.ne_one
  · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, ← hα, rootOfSplitsXPowSubC_pow, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

include hIrr hrF in
/-- Since `L/ℚ` is abelian, `σ_a(μ) = ξ ^ p * μ ^ a` for every `σ_a ∈ Gal(F/ℚ)`, with `ξ ∈ F`
nonzero. -/
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
  simp only [AlgEquiv.mul_apply, AlgEquiv.coe_restrictScalars] at hmain
  rw [hτα, MulAction.subgroup_smul_def, Units.smul_def, Algebra.smul_def, map_mul,
    AlgEquiv.liftNormal_commutes, Rat.galEquivZMod_apply_of_pow_eq p _ _ hζ.pow_eq_one,
      map_pow] at hmain
  obtain ⟨c, j, hj, h⟩ := exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap hF hIrr (α := α)
    (β := σ.liftNormal L α) (by rw [rootOfSplitsXPowSubC_pow])
    (by rw [← map_pow, hα, IsScalarTower.algebraMap_apply (𝓞 F) F, AlgEquiv.liftNormal_commutes])
  have hc : algebraMap F L c ≠ 0 := by
    contrapose hα₀
    rwa [hα₀, zero_mul, map_eq_zero] at h
  rw [h, map_mul, map_pow, hτα, AlgEquiv.commutes, MulAction.subgroup_smul_def, Units.smul_def,
    Algebra.smul_def, mul_pow, ← mul_assoc, ← mul_assoc, mul_left_inj' (pow_ne_zero j hα₀),
      mul_comm,
    mul_right_inj' hc, ← map_pow, ← map_pow,
      (FaithfulSMul.algebraMap_injective F L).eq_iff] at hmain
  refine ⟨c, by rwa [_root_.map_ne_zero] at hc, ?_⟩
  apply FaithfulSMul.algebraMap_injective F L
  rw [← AlgEquiv.liftNormal_commutes, ← rootOfSplitsXPowSubC_pow (n := p) (algebraMap (𝓞 F) F μ) L,
    map_pow, h, mul_pow, pow_right_comm, map_mul, map_pow, map_pow, rootOfSplitsXPowSubC_pow,
    hζ.pow_inj (ZMod.val_lt _) hj hmain]

include hμ hrF hIrr in
/-- If `𝔮` is a prime of `𝓞 F` with `p ∤ v_𝔮(μ)`, then every `σ ∈ Gal(F/ℚ)` fixing `𝔮` is the
identity. -/
lemma kw_split_prime {𝔮 : Ideal (𝓞 F)} (h𝔮 : Prime 𝔮)
    (hv : ¬ p ∣ multiplicity 𝔮 (span {(μ : 𝓞 F)})) {σ : Gal(F/ℚ)} (hσ : σ • 𝔮 = 𝔮) :
    σ = 1 := by
  obtain ⟨𝔞, h𝔞⟩ := pow_multiplicity_dvd 𝔮 (span {(μ : 𝓞 F)})
  obtain ⟨ξ, hξ₀, hξ⟩ := kw_abelian_kummer p F hrF hIrr σ
  obtain ⟨d, hd₀, ⟨β, hβ⟩⟩ := exists_integer_multiple ξ
  have hβ₀ : β ≠ 0 := by
    by_contra this
    simp [this, hd₀, hξ₀] at hβ
  replace hβ : σ • (d ^ p * μ) = β ^ p * μ ^ (Rat.galEquivZMod p F σ).val.val := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, MulSemiringAction.smul_mul, map_mul, algebraMap.smul', algebraMap.smul', map_pow,
      map_intCast, AlgEquiv.smul_def, map_pow, map_intCast, AlgEquiv.smul_def, hξ, map_pow, hβ,
      ← mul_assoc, ← mul_pow, map_pow]
  have hf𝔮 : FiniteMultiplicity 𝔮 𝔮 := FiniteMultiplicity.of_prime_left h𝔮 h𝔮.ne_zero
  have hfμ : FiniteMultiplicity 𝔮 (span {μ}) := FiniteMultiplicity.of_prime_left h𝔮 <| by simpa
    using hμ
  have hfβ : FiniteMultiplicity 𝔮 (span {β}) := FiniteMultiplicity.of_prime_left h𝔮 <| by simpa
    using hβ₀
  have hσ𝔞 : multiplicity 𝔮 (σ • 𝔞) = 0 := by
    rw [← hσ, pointwise_smul_def', pointwise_smul_def', multiplicity_map_eq]
    have := congr_arg (multiplicity 𝔮 · ) h𝔞
    rwa [multiplicity_mul h𝔮 (by rwa [← h𝔞]), hf𝔮.multiplicity_pow h𝔮, multiplicity_self,
      mul_one, Nat.left_eq_add] at this
  have h𝔞₀ : 𝔞 ≠ 0 := by
    contrapose! h𝔞
    simpa [h𝔞]
  have hσ𝔞₀ : σ • 𝔞 ≠ 0 := (smul_ne_zero_iff_ne σ).mpr h𝔞₀
  have h₁ := congr_arg (multiplicity 𝔮 · ) <| congr_arg (σ • · ) <|
    congr_arg (span {(d ^ p : 𝓞 F)} * · ) h𝔞
  rw [span_singleton_mul_span_singleton, smul_mul', multiplicity_mul h𝔮, smul_mul', smul_pow', hσ,
    multiplicity_mul h𝔮, smul_closure, smul_closure, Set.smul_set_singleton, Set.smul_set_singleton, smul_pow', ← span_singleton_pow,
    FiniteMultiplicity.multiplicity_pow h𝔮, multiplicity_pow_self h𝔮.ne_zero h𝔮.not_isUnit, hβ,
    ← span_singleton_mul_span_singleton, multiplicity_mul h𝔮, ← span_singleton_pow,
    ← span_singleton_pow, FiniteMultiplicity.multiplicity_pow h𝔮 hfβ,
    FiniteMultiplicity.multiplicity_pow h𝔮 hfμ, hσ𝔞, add_zero] at h₁
  · replace h₁ := congr_arg ((↑) : _ → ZMod p) h₁
    simp only [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, ZMod.natCast_val,
      ZMod.cast_id', id_eq,
      zero_add] at h₁
    rw [mul_eq_right₀] at h₁
    · rwa [← (Rat.galEquivZMod p F).apply_eq_iff_eq, map_one, Units.ext_iff, Units.val_one]
    · rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  · have h₃ := congr_arg ( · ^ (Rat.galEquivZMod p F σ).val.val) h𝔞
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
include hrF hIrr hμ in
/-- If `L` is unramified outside `p`, then `p ∣ v_𝔮(μ)` for every prime `𝔮` of `𝓞 F`. -/
lemma kw_mu_val_p (𝔮 : Ideal (𝓞 F)) [𝔮.IsMaximal] (hLRam : UnramifiedOutside L p) (hp' : Odd p) :
    p ∣ multiplicity 𝔮 (span {μ}) := by
  let q := absNorm (under ℤ 𝔮)
  have : 𝔮.LiesOver (span {(q : ℤ)}) := Int.liesOver_span_absNorm 𝔮
  have h𝔮 : Prime 𝔮 := prime_of_isMaximal 𝔮
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
    contrapose hσ'
    exact kw_split_prime p F hrF hμ hIrr h𝔮 hσ' hσ
  · obtain ⟨𝔔, _, _⟩  := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔮
    have : 𝔔.LiesOver (span {(q : ℤ)}) := LiesOver.trans 𝔔 𝔮 _
    have h𝔔 : Prime 𝔔 := prime_of_isMaximal 𝔔
    have h𝔔' : 𝔔.ramificationIdx (𝓞 F) = 1 := by
      have hram : 𝔔.ramificationIdx ℤ = 1 :=
        (hLRam q hq.out hqp).ramificationIdx_eq_one ‹𝔔.LiesOver (span {(q : ℤ)})›
      have htower := Ideal.ramificationIdx_tower (R := ℤ) 𝔮 𝔔
      rw [hram, IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q F 𝔮
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
/-- If `L` is unramified outside `p`, then `(μ) = 𝔞 ^ p` for a nonzero ideal `𝔞` of `𝓞 F`. -/
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

end IsScalarTower

noncomputable section ScalarTowerBridge

variable (p : ℕ) [hp : Fact p.Prime]
variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [IsCyclotomicExtension {p} ℚ F] [IsGalois ℚ L]

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

end ScalarTowerBridge
