module

public import Mathlib.NumberTheory.RamificationInertia.Galois

public import SKW.Stickelberger.valGauss

@[expose] public section

noncomputable section

open Ideal NumberField IntermediateField Pointwise IsCyclotomicExtension.Rat

variable (p f : ℕ) [NeZero (p ^ f - 1)]

local notation3 "𝒑" => span {(p : ℤ)}

variable {p f}

variable {L : Type*} [Field L] [NumberField L] {F K : IntermediateField ℚ L} {P : Ideal (𝓞 K)}

variable (hbij : Function.Bijective (rootsOfUnity.mapQuot (p ^ f - 1) P))

variable {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p) {η : 𝓞 K} (hη : IsPrimitiveRoot η (p ^ f - 1))

variable [P.IsMaximal] (𝓟 : Ideal (𝓞 L)) [hp : Fact (p.Prime)]

local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

variable (m d : ℕ) (hmf : orderOf (p : ZMod m) = f) (hdm : p ^ f - 1 = d * m)

variable {E : IntermediateField ℚ L} [IsCyclotomicExtension {m * p} ℚ E] (𝔓 : Ideal (𝓞 E))

variable {k : IntermediateField ℚ L} (𝔭 : Ideal (𝓞 k))

include hη hdm in
theorem smul_gaussSum_eq_gaussSum' [NeZero f] [NeZero m] [Fact (Odd p)] [IsCyclotomicExtension {p} ℚ F]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [IsCyclotomicExtension {p ^ f - 1} ℚ K] [P.LiesOver 𝒑]
    [Algebra F E] [IsScalarTower F E L] (τ : Gal(L/E)) :
    τ • (GaussSum hbij hζ d ^ m) = GaussSum hbij hζ d ^ m := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p * (p ^ f - 1)} ℚ L
  convert_to (τ.restrictScalars F) • (GaussSum hbij hζ d ^ m) = _
  rw [smul_pow', gal_gaussSum_eq_gaussSum hbij hζ hη]
  obtain ⟨k, hk⟩ : ∃ k, (d : ℤ) *
      (galFEquiv p f K (τ.restrictScalars F)).val.val = d + (p ^ f - 1 : ℕ) * k := by
    have t₀ : τ.restrictScalars F • algebraMap (𝓞 K) (𝓞 L) (η ^ d) =
        algebraMap (𝓞 K) (𝓞 L) (η ^ d) := by
      apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [algebraMap.smul', ← IsScalarTower.algebraMap_apply]
      obtain ⟨x, hx⟩ : ∃ x : E, algebraMap (𝓞 K) L (η ^ d) = algebraMap E L x := by
        let ε := IsCyclotomicExtension.zeta (m * p) ℚ E
        have hε := IsCyclotomicExtension.zeta_spec (m * p) ℚ E
        replace hε := hε.map_of_injective <| FaithfulSMul.algebraMap_injective E L
        obtain ⟨i, -, hi⟩ := hε.eq_pow_of_pow_eq_one (ξ := algebraMap (𝓞 K) L (η ^ d))
          (by
            rw [← map_pow, ← pow_mul, ← mul_assoc, ← hdm, pow_mul, hη.pow_eq_one, one_pow, map_one])
        refine ⟨ε ^ i, ?_⟩
        rw [map_pow _ ε, hi]
      rw [hx, AlgEquiv.smul_def, AlgEquiv.coe_restrictScalars', AlgEquiv.commutes]
    have := congr_arg (· ^ d) <| galLFEquiv_apply_eta p f hη (τ.restrictScalars F)
    dsimp only at this
    rw [← map_pow, ← map_pow, ← smul_pow', ← map_pow, t₀, ← pow_mul,
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)).eq_iff,
      ← pow_mod_orderOf _ d, ← pow_mod_orderOf _ (_ * d), ← hη.eq_orderOf] at this
    have := congr_arg ((↑) : ℕ → ℤ) <| hη.pow_inj (Nat.mod_lt _ <| NeZero.pos (p ^ f - 1))
      (Nat.mod_lt _ <| NeZero.pos (p ^ f - 1)) this
    rwa [Int.natCast_mod, Int.natCast_mod, Int.natCast_mul, ← Int.ModEq,
      Int.modEq_iff_add_fac, mul_comm] at this
  rw [hk, GaussSum_periodic hbij hζ hη]
  exact Dvd.intro k rfl

include hη in
theorem smul_gaussSum_eq_mul_gaussSum [P.LiesOver 𝒑] (τ : Gal(L/K)) {e : ℕ} (he : ¬ p ∣ e)
    (h : τ • algebraMap (𝓞 F) (𝓞 L) ζ = algebraMap (𝓞 F) (𝓞 L) ζ ^ e) :
    τ • GaussSum hbij hζ d =
      algebraMap (𝓞 K) (𝓞 L) ((teichmuller hbij ^ d) e) * GaussSum hbij hζ d := by
  let u : (𝓞 K ⧸ P)ˣ := IsUnit.unit (a := e) (by
    rw [isUnit_iff_ne_zero]
    simpa [CharP.cast_eq_zero_iff, Ideal.ringChar_quot, ← (liesOver_iff P 𝒑).mp inferInstance])
  have hu : (u : 𝓞 K ⧸ P) = (e : 𝓞 K ⧸ P) := IsUnit.unit_spec _
  have : algebraMap (𝓞 K) (𝓞 L) ((teichmuller hbij ^ (-(d : ℤ))) ↑e) ≠ 0 := by
    rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    exact teichmuller_zpow_apply_ne_zero hbij (-d) u
  refine mul_left_cancel₀ this ?_
  rw [← mul_assoc, ← map_mul, ← MulChar.mul_apply, zpow_neg, ← zpow_natCast, zpow_natCast,
    inv_mul_cancel, MulChar.one_apply (by exact Units.isUnit u), map_one, one_mul]
  convert gaussSum_mulShift ((teichmuller hbij ^ (-(d : ℤ))).ringHomComp (algebraMap (𝓞 K) (𝓞 L)))
    ((algebraMap (𝓞 F) (𝓞 L)).compAddChar (addCharTrace P hζ)) u
  · simp [hu]
  · simp_rw [GaussSum, gaussSum, Finset.smul_sum, smul_mul']
    congr! with x
    · rw [smul_eq_galRestrict_apply (𝓞 K), map_teichmuller_zpow_eq hbij _ _ 1 one_ne_zero hη (by simp),
        Nat.cast_one, mul_one]
    · rw [smul_eq_galRestrict_apply (𝓞 K), algebraMap_comp_addCharTrace,
        monoidHom_comp_addCharTrace_eq_mulShift _ _ _ e]
      · simp [hu]
      · rwa [smul_eq_galRestrict_apply (𝓞 K)] at h

include hη hdm in
theorem smul_gaussSum_eq_gaussSum [NeZero m] [P.LiesOver 𝒑] (τ : Gal(L/K)) :
    τ • (GaussSum hbij hζ d ^ m) = GaussSum hbij hζ d ^ m := by
  obtain ⟨e, he₁, he₂⟩ : ∃ e, ¬ p ∣ e ∧
      τ • algebraMap (𝓞 F) (𝓞 L) ζ = algebraMap (𝓞 F) (𝓞 L) ζ ^ e := by
    rw [smul_eq_galRestrict_apply (𝓞 K)]
    replace hζ : IsPrimitiveRoot (algebraMap (𝓞 F) (𝓞 L) ζ) p :=
      hζ.map_of_injective (FaithfulSMul.algebraMap_injective _ _)
    refine ⟨(hζ.autToPow (𝓞 K) ((galRestrict (𝓞 K) (K) L (𝓞 L)) τ)).val.val, ?_,
      (hζ.autToPow_spec _ _).symm⟩
    rw [← hp.out.coprime_iff_not_dvd, Nat.coprime_comm]
    exact ZMod.val_coe_unit_coprime _
  have : IsUnit (e : 𝓞 K ⧸ P) := by
    rw [isUnit_iff_ne_zero]
    simpa [CharP.cast_eq_zero_iff, Ideal.ringChar_quot, ← (liesOver_iff P 𝒑).mp inferInstance]
  rw [smul_pow', smul_gaussSum_eq_mul_gaussSum hbij hζ hη _ _ he₁ he₂, mul_pow, ← map_pow,
    ← MulChar.pow_apply' _ (NeZero.ne m), ← pow_mul, ← hdm, show teichmuller hbij ^ (p ^ f - 1) = 1 by
        convert pow_orderOf_eq_one (teichmuller hbij)
        exact (orderOf_teichmuller hbij hη).symm,
    MulChar.one_apply this, map_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
include hη hdm in
  theorem lemma37 [NeZero f] [NeZero m] [Fact (Odd p)] [Algebra F E] [IsScalarTower F E L]
    [P.LiesOver 𝒑] [IsCyclotomicExtension {m} ℚ k]
    [IsCyclotomicExtension {p} ℚ F]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [IsCyclotomicExtension {p ^ f - 1} ℚ K] :
    ∃ Γ : 𝓞 k, GaussSum hbij hζ d ^ m = algebraMap (𝓞 k) (𝓞 L) Γ := by
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {p * (p ^ f - 1)} ℚ L
  suffices ↑(GaussSum hbij hζ d ^ m : 𝓞 L) ∈ k from
    ⟨⟨⟨(GaussSum hbij hζ d ^ m : 𝓞 L), this⟩,
      coe_isIntegral_iff.mp <| RingOfIntegers.isIntegral_coe _⟩, rfl⟩
  have : k = E ⊓ K := by
    refine (eq_of_le_iff_finrank_eq (le_inf_iff.mpr ⟨?_, ?_⟩)).mpr ?_
    · exact isCyclotomicExtension_le_of_dvd ℚ L m (m * p) k E <| dvd_mul_right m p
    · exact isCyclotomicExtension_le_of_dvd ℚ L m (p ^ f - 1) k K <| dvd_of_mul_left_eq d hdm.symm
    · rw [IsCyclotomicExtension.Rat.finrank m k]
      

      sorry
  rw [this, IntermediateField.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [RingOfIntegers.coe_eq_algebraMap]
    obtain ⟨x, hx⟩ := (IsGaloisGroup.isInvariant (A := 𝓞 E)).isInvariant
      (GaussSum hbij hζ d ^ m)
        fun τ : Gal(L/E) ↦ smul_gaussSum_eq_gaussSum' hbij hζ hη m d hdm τ
    simp [← hx, ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 E) E L,
      IntermediateField.algebraMap_apply]
  · rw [RingOfIntegers.coe_eq_algebraMap]
    obtain ⟨x, hx⟩ := (IsGaloisGroup.isInvariant (A := 𝓞 K)).isInvariant
      (GaussSum hbij hζ d ^ m) fun τ : Gal(L/K) ↦ smul_gaussSum_eq_gaussSum hbij hζ hη m d hdm τ
    simp [← hx, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 K) K L,
      IntermediateField.algebraMap_apply]

theorem lemma38 [Algebra E L] [𝓟.LiesOver 𝒑] [𝓟.LiesOver 𝔓] :
    ramificationIdx 𝔓 𝓟 = 1 := sorry

theorem lemma39 [Algebra k E] [𝔓.LiesOver 𝔭] [𝔓.LiesOver 𝒑] :
    ramificationIdx 𝔭 𝔓 = p - 1 := sorry

variable (p) in
theorem lemma40_1 [IsCyclotomicExtension {m} ℚ k] [NeZero m] (hp' : p.Coprime m) :
    MulEquiv.mapSubgroup (galEquivZMod m k) (MulAction.stabilizer Gal(k/ℚ) 𝔭) =
      Subgroup.zpowers (ZMod.unitOfCoprime p hp') := sorry

theorem lemma40_2 [IsCyclotomicExtension {m} ℚ k] [NeZero m] (a : (ZMod m)ˣ) (hp' : p.Coprime m)
    (b : Subgroup.zpowers (ZMod.unitOfCoprime p hp')) :
    (galEquivZMod m k).symm (a * b) • 𝔭 = (galEquivZMod m k).symm a • 𝔭 := sorry

theorem lemma41 [IsCyclotomicExtension {m} ℚ k] [NeZero m] [P.LiesOver 𝒑] (a : (ZMod m)ˣ) {Γ : 𝓞 k}
    (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 k) (𝓞 L) Γ) :
    emultiplicity (((galEquivZMod m k).symm a⁻¹) • 𝔭) (span {Γ}) =
      ∑ j ∈ Finset.range f, (a.val.val * p ^ j) % m := sorry

theorem lemma42 [IsCyclotomicExtension {m} ℚ k] [NeZero m] (a : (ZMod m)ˣ) :
    emultiplicity (((galEquivZMod m k).symm a)⁻¹ • 𝔭)
      (∏ a, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val) =
        ∑ j ∈ Finset.range f, (a.val.val * p ^ j) % m := sorry

variable [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p ^ f - 1} ℚ K] [NeZero f] [𝓟.IsPrime]

include hη 𝓟 in
theorem lemma43_1 [P.LiesOver 𝒑] {𝔭 : Ideal (𝓞 k)} [NeZero 𝓟]
    [𝓟.LiesOver 𝔭] {Γ : 𝓞 k} (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 k) (𝓞 L) Γ)
    (hP₀ : Prime 𝔭) (hP₀' : ¬ 𝔭.LiesOver 𝒑) :
    emultiplicity 𝔭 (span {Γ}) = 0 := by
  have h𝓟 : Prime 𝓟 := (prime_iff_isPrime (NeZero.ne _)).mpr inferInstance
  have : emultiplicity 𝓟 (span {GaussSum hbij hζ d ^ m}) = 0 := by
    have : ¬ 𝓟.LiesOver 𝒑 := by
      contrapose! hP₀'
      exact LiesOver.tower_bot 𝓟 𝔭 𝒑
    have := valGauss_eq_zero_of_not_liesOver hbij hζ hη 𝓟 this d
    rw [valGauss] at this
    rw [← span_singleton_pow, emultiplicity_pow h𝓟, this, mul_zero]
  rw [hΓ, ← Set.image_singleton, ← map_span] at this
  rw [IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul' _ hP₀.irreducible h𝓟.irreducible
    (NeZero.ne _)] at this
  apply eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ this
  rw [Nat.cast_ne_zero]
  apply IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
  exact hP₀.ne_zero

theorem lemma43_2 [IsCyclotomicExtension {m} ℚ k] [NeZero m] {𝔮 : Ideal (𝓞 k)} (hQ₀ : Prime 𝔮) :
    emultiplicity 𝔮 (∏ a, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val) =
      ∑ a, if (galEquivZMod m k).symm a • 𝔮 = 𝔭 then a.val.val else 0 := sorry

variable (K) in
theorem lemma43_3 (σ : Gal(k/ℚ)) :
    ∃ τ : Gal(L/K), σ • 𝔭 = comap (algebraMap (𝓞 k) (𝓞 L)) (τ • 𝓟) := sorry

theorem lemma43_4 [NeZero m] (b : (ZMod m)ˣ) (hp' : p.Coprime m) (g : (ZMod m)ˣ → ℕ) :
    ∑ a with a * b⁻¹ ∈ Finset.image (fun x ↦ ZMod.unitOfCoprime p hp' ^ x)
      (Finset.range f), g a = ∑ j ∈ Finset.range f, g (b * (ZMod.unitOfCoprime p hp') ^ j) := by
  sorry
  -- have hord : orderOf (ZMod.unitOfCoprime p hp') = f := by
  --   rwa [← orderOf_units, ZMod.coe_unitOfCoprime]
  -- FIXME: this cannot work since (ZMod m)ˣ is not an AddCommMonoid
  -- rw [← Finset.sum_image (f := fun j => b * ZMod.unitOfCoprime p hp' ^ j)]
  -- · congr 1
  --   ext a
  --   simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
  --   constructor
  --   · rintro ⟨j, hj, hjb⟩
  --     exact ⟨j, hj, by rw [hjb]; group⟩
  --   · rintro ⟨j, hj, rfl⟩
  --     exact ⟨j, hj, by group⟩
  -- · intro j₁ hj₁ j₂ hj₂ heq
  --   have hpow : ZMod.unitOfCoprime p hp' ^ j₁ = ZMod.unitOfCoprime p hp' ^ j₂ :=
  --     mul_left_cancel heq
  --   rcases le_or_lt j₁ j₂ with h | h
  --   · have h0 : ZMod.unitOfCoprime p hp' ^ (j₂ - j₁) = 1 :=
  --       mul_left_cancel (a := ZMod.unitOfCoprime p hp' ^ j₁)
  --         (by rw [mul_one, ← pow_add, Nat.add_sub_cancel' h, hpow])
  --     have hdvd := orderOf_dvd_of_pow_eq_one h0
  --     rw [hord] at hdvd; omega
  --   · have h0 : ZMod.unitOfCoprime p hp' ^ (j₁ - j₂) = 1 :=
  --       mul_left_cancel (a := ZMod.unitOfCoprime p hp' ^ j₂)
  --         (by rw [mul_one, ← pow_add, Nat.add_sub_cancel' h.le, ← hpow])
  --     have hdvd := orderOf_dvd_of_pow_eq_one h0
  --     rw [hord] at hdvd; omega

omit [𝓟.IsPrime] in
include hη hdm hmf in
theorem GaussSum_factorization [IsCyclotomicExtension {m} ℚ k] [NeZero m] [NeZero 𝓟] [P.LiesOver 𝒑]
    [𝔭.IsPrime] [𝓟.LiesOver 𝔭] [𝔭.LiesOver 𝒑] (Γ : 𝓞 k)
    (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 k) (𝓞 L) Γ) :
    span {Γ} = ∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val := by
  rw [UniqueFactorizationMonoid.eq_iff_emultiplicity_eq]
  intro 𝔮 hQ₀
  have : 𝔮.IsMaximal := (isPrime_of_prime hQ₀).isMaximal hQ₀.ne_zero
  by_cases hP₀' : 𝔮.LiesOver 𝒑
  · have := IsCyclotomicExtension.isGalois {m} ℚ k
    have hp' : p.Coprime m := (coprime_pow_sub_one p f).symm.of_dvd_right <| Dvd.intro_left d hdm.symm
    obtain ⟨σ, rfl⟩ : ∃ σ : Gal(k/ℚ), 𝔮 = σ⁻¹ • 𝔭 := by
      obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝒑 𝔭 𝔮 Gal(k/ℚ)
      exact ⟨σ⁻¹, by rw [inv_inv]⟩
    rw [lemma43_2 _ _ hQ₀]
    obtain ⟨b, hb⟩ : ∃ b, σ⁻¹ = (galEquivZMod m k).symm b⁻¹ :=
      ⟨galEquivZMod m k σ, by rw [map_inv, MulEquiv.symm_apply_apply]⟩
    rw [hb, lemma41 hbij hζ m d 𝔭 _ hΓ]
    simp_rw [smul_smul, ← map_mul, ← MulAction.mem_stabilizer_iff]
    simp_rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs =>
      enter [1, 1, 1, x]
      rw [← Subgroup.mem_map_equiv, ← MulEquiv.coe_mapSubgroup, lemma40_1 p m 𝔭 hp']
    have t₁ : orderOf (ZMod.unitOfCoprime p hp') = f := by
      rwa [← orderOf_units, ZMod.coe_unitOfCoprime]
    have t₂ : IsOfFinOrder (ZMod.unitOfCoprime p hp') := by
      exact isOfFinOrder_of_finite (ZMod.unitOfCoprime p hp')
    simp_rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf t₂, t₁, lemma43_4]
    simp [← ZMod.val_natCast]
  · obtain ⟨𝓠, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔮
    have {σ : Gal(k/ℚ)} : σ • 𝔮 ≠ 𝔭 := by
      contrapose! hP₀'
      rw [(smul_eq_iff_eq_inv_smul _).mp hP₀']
      exact LiesOver.smul σ⁻¹
    rw [lemma43_1 hbij hζ hη 𝓠 m d hΓ hQ₀ hP₀', lemma43_2 m 𝔭 hQ₀, Nat.cast_sum]
    simp [if_neg this]

#exit





  ·







    have t₁ : orderOf (ZMod.unitOfCoprime p hp') = f := by
      rwa [← orderOf_units, ZMod.coe_unitOfCoprime]
    have t₂ : IsOfFinOrder (ZMod.unitOfCoprime p hp') := by
      exact isOfFinOrder_of_finite (ZMod.unitOfCoprime p hp')
    simp_rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf t₂, t₁]
    simp_rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, lemma43_4]
    simp [← ZMod.val_natCast]
  · obtain ⟨𝓠, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P₀
    have {σ : Gal(E₀/ℚ)} : σ • P₀ ≠ tP₀ := by
      contrapose! hP₀'
      rw [(smul_eq_iff_eq_inv_smul _).mp hP₀']
      exact LiesOver.smul σ⁻¹
    rw [lemma43_1 hbij hζ hη 𝓠 m d hΓ hP₀ hP₀', lemma43_2 m tP₀ hP₀, Nat.cast_sum]
    simp [if_neg this]

#exit

-- example [𝓟.IsPrime] [𝓟.LiesOver 𝒑] [P.LiesOver ]
variable (p f) in
theorem card_stabilizer_eq (𝓠 : Ideal (𝓞 L)) [𝓠.LiesOver 𝒑] :
    Fintype.card { σ : Gal(L/F) // 𝓠 = σ • 𝓟 } = f := sorry

variable [NeZero f] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]
  [IsCyclotomicExtension {p ^ f - 1} ℚ K]

include hη in
theorem span_GaussSum_factorization [𝓟.IsPrime] [NeZero 𝓟] [𝓟.LiesOver P] [P.LiesOver 𝒑]
    [Fact (Odd p)] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    span {GaussSum hbij hζ a} ^ f =
      ∏ σ : Gal(L/F), (σ • 𝓟) ^ (valGauss hbij hζ 𝓟 (a * (galFEquiv p f K σ⁻¹).val.val)).toNat := by
  classical
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have h {σ : Gal(L/F)} : Prime (σ • 𝓟) :=
    (prime_iff_isPrime ((smul_ne_zero_iff_ne _).mpr (NeZero.ne 𝓟))).mpr inferInstance
  rw [UniqueFactorizationMonoid.eq_iff_emultiplicity_eq]
  intro 𝓠 hQ
  rw [emultiplicity_pow hQ, ← valGauss, Finset.emultiplicity_prod hQ]
  simp_rw [emultiplicity_pow hQ]
  have : 𝓠.IsPrime := isPrime_of_prime hQ
  by_cases hQ' : 𝓠.LiesOver 𝒑
  · simp_rw [← emultiplicity_smul_GaussSum hbij hζ hη 𝓟, hQ.emultiplicity_prime h,
      associated_iff_eq, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    rw [Finset.sum_filter_eq_eq_nsmul_card (α := Gal(L/F)) (b := 𝓠) (γ := ℕ∞)
      (fun σ ↦ σ • 𝓟)
      (fun I ↦ ↑(emultiplicity I (span {GaussSum hbij hζ a})).toNat)]
    rw [card_stabilizer_eq p f]
    rw [← valGauss, ENat.coe_toNat]
    rw [nsmul_eq_mul]
    exact valGauss_ne_top hbij hζ hη 𝓟 𝓠 hQ _
  · rw [valGauss_eq_zero_of_not_liesOver hbij hζ 𝓠 hQ' _ ha, mul_zero,
      eq_comm, Finset.sum_eq_zero]
    intro _ _
    refine mul_eq_zero_of_right _ ?_
    rw [emultiplicity_eq_zero, prime_dvd_prime_iff_eq hQ h]
    contrapose! hQ'
    rw [hQ']
    exact Ideal.LiesOver.smul _

#exit

variable (m d : ℕ) [NeZero m] (hmd : p ^ f - 1 = m * d)


example [P.LiesOver 𝒑] :
    GaussSum hbij hζ d ∈ Algebra.adjoin ℤ {algebraMap (𝓞 F) (𝓞 L) ζ,
      algebraMap (𝓞 K) (𝓞 L) η ^ d} := by
  simp only [GaussSum, gaussSum, zpow_neg, zpow_natCast, MulChar.ringHomComp_apply,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe, Function.comp_apply]
  refine Subalgebra.sum_mem _ fun x _ ↦ ?_
  sorry

example [P.LiesOver 𝒑] :
    ↑(GaussSum hbij hζ d) ∈ ℚ⟮algebraMap (𝓞 F) L ζ⟯ ⊔ ℚ⟮algebraMap (𝓞 K) L η ^ d⟯ := by
  simp only [GaussSum, gaussSum, zpow_neg, zpow_natCast, MulChar.ringHomComp_apply,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe, Function.comp_apply,
    map_sum, map_mul, ← IsScalarTower.algebraMap_apply]
  refine IntermediateField.sum_mem _ fun x _ ↦ IntermediateField.mul_mem _ ?_ ?_
  · have hηm : IsPrimitiveRoot (η ^ d) m := sorry
    have : ((teichmuller hbij ^ d)⁻¹) ^ m = 1 := sorry
    have := MulChar.apply_mem_algebraAdjoin_of_pow_eq_one this hηm x
    sorry
  · sorry

theorem step2 [P.LiesOver 𝒑] (τ : Gal(L/K)) :
    τ • (GaussSum hbij hζ d ^ m) = GaussSum hbij hζ d ^ m := sorry

variable {E : Type*} [Field E] [NumberField E] [IsCyclotomicExtension {m} ℚ E]

theorem step3 [P.LiesOver 𝒑] [Algebra E L] :
    ∃ Γ : 𝓞 E, GaussSum hbij hζ d ^ m = algebraMap (𝓞 E) (𝓞 L) Γ := sorry

def θ : Gal(E/ℚ) → ℕ := sorry

variable [IsAbelianGalois ℚ E] [IsAbelianGalois ℚ K] [Algebra E K]

variable (K) in
def GalLift  : Gal(E/ℚ) → Gal(L/F) :=
  fun τ ↦ (galEquiv₀ p f F K).symm <| (τ.restrictNormalHom_surjective K).choose

-- theorem GalLift_algebraMap_smul (τ : Gal(E/ℚ)) (I : Ideal (𝓞 E)) :
--     map (algebraMap (𝓞 E) (𝓞 L)) (τ • I) = GalLift K τ • (map (algebraMap (𝓞 E) (𝓞 L)) I) := by
--   sorry

open MulAction

variable (F) in
def step4_1 (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] [Algebra E L] :
    orbit Gal(L/F) 𝓟 ≃ P₀.primesOver (𝓞 L) := sorry

theorem step4_2 (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] [Algebra E L] (𝓠 : orbit Gal(L/F) 𝓟) :
    step4_1 F 𝓟 P₀ 𝓠 = 𝓠.1 := by sorry

theorem step4_3 (t : Gal(L/F) → ℕ) (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] [Algebra E L] :
    ∏ σ : Gal(L/F), (σ • 𝓟) ^ (t σ) =
      ∏ 𝓠 : P₀.primesOver (𝓞 L), 𝓠.1 ^
       ∑ s, t ((orbitProdStabilizerEquivGroup Gal(L/F) 𝓟) ((step4_1 F 𝓟 P₀).symm 𝓠, s)) := by
  classical
  let : Fintype (orbit Gal(L/F) 𝓟) := Set.Finite.fintype <| Finite.finite_mulAction_orbit _
  rw [← (MulAction.orbitProdStabilizerEquivGroup Gal(L/F) 𝓟).prod_comp, Fintype.prod_prod_type]
  simp_rw [MulAction.orbitProdStabilizerEquivGroup_apply_smul, Finset.prod_pow_eq_pow_sum]
  rw [← Equiv.prod_comp (step4_1 F 𝓟 P₀)]
  refine Fintype.prod_congr _ _ ?_
  intro 𝓠
  simp [step4_2]

example (hq : p.Coprime (p ^ f - 1)) [P.LiesOver 𝒑 ]:
    stabilizer Gal(L/F) 𝓟 ≃ Subgroup.zpowers (ZMod.unitOfCoprime p hq) := by
  have := IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (p ^ f - 1) K p P hq

example {𝓠 : Ideal (𝓞 L)} {σ : Gal(L/F)} (hσ : σ • 𝓟 = 𝓠) (a : ℤ) [P.LiesOver 𝒑] :
    ∑ s, (valGauss hbij hζ 𝓟 (a *
      (galFEquiv p f K (orbitProdStabilizerEquivGroup Gal(L/F) 𝓟 (⟨𝓠, ⟨σ, hσ⟩⟩, s))⁻¹).val.val)).toNat =
    f * (valGauss hbij hζ 𝓟 (a * (galFEquiv p f K σ⁻¹).val.val)).toNat := by
  have (s : stabilizer Gal(L/F) 𝓟) :
    ∃ k : ℕ, galFEquiv p f K (orbitProdStabilizerEquivGroup Gal(L/F) 𝓟 (⟨𝓠, ⟨σ, hσ⟩⟩, s))⁻¹ =
      (p : ZMod (p ^ f - 1)) ^ k * galFEquiv p f K σ := sorry
  rw [Finset.sum_congr rfl]


  sorry
  intro s _
  obtain ⟨k, hk⟩ := this s
  rw [hk]





include hη in
set_option backward.isDefEq.respectTransparency false in
theorem step4 [𝓟.IsPrime] [NeZero 𝓟] [𝓟.LiesOver P] [P.LiesOver 𝒑] [Algebra E L] [Fact (Odd p)]
    {Γ : 𝓞 E} (hΓ : GaussSum hbij hζ d ^ m = algebraMap (𝓞 E) (𝓞 L) Γ) (P₀ : Ideal (𝓞 E))
    [P₀.IsMaximal] [P₀.LiesOver 𝒑] (hP₀ : ¬ P₀ ∣ span {(m : 𝓞 E)}) :
    span {Γ ^ f} = ∏ τ : Gal(E/ℚ), (τ • P₀) ^ (m * f * θ τ) := by
  have : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) := sorry
  have : Function.Injective (Ideal.map (algebraMap (𝓞 E) (𝓞 L))) := sorry
  apply this
  rw [map_span, Set.image_singleton, map_pow, ← hΓ, ← span_singleton_pow, ← span_singleton_pow,
    pow_right_comm, span_GaussSum_factorization hbij hζ hη 𝓟 d, ← Finset.prod_pow]

  simp_rw [← pow_mul]
  rw [step4_3 𝓟 _ P₀]




  have : P₀ ≠ 0 := sorry

  simp_rw [← Ideal.mapHom_apply, map_prod, map_pow, mapHom_apply]

  simp_rw [Ideal.map_algebraMap_eq_finsetProd_pow this, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_set_coe]
  congr! with I



#exit
  rw [this, ← Ideal.mapHom_apply, map_prod]
  simp_rw [map_pow, mapHom_apply]
  have : P₀ ≠ 0 := sorry
  simp_rw [Ideal.map_algebraMap_eq_finsetProd_pow this, ← Finset.prod_pow]

  rw [Finset.prod_comm]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum]
--  let : MulSemiringAction Gal(L/F) (𝓞 L) := by
--    exact RingOfIntegers.instMulSemiringAction L
--  let : SMulCommClass Gal(L/F) (𝓞 F) (𝓞 L) := by sorry
--  let := Ideal.instMulActionElemPrimesOver (G := Gal(L/F)) (p := under (𝓞 F) 𝓟) (B := 𝓞 L)
  let p₀ : Ideal (𝓞 F) := under (𝓞 F) 𝓟
  let 𝓟₀ : p₀.primesOver (𝓞 L) := primesOver.mk p₀ 𝓟
  let e := MulAction.orbitProdStabilizerEquivGroup Gal(L/F) 𝓟₀
  let : Fintype (MulAction.orbit Gal(L/F) 𝓟₀) := sorry
  let : Fintype (MulAction.stabilizer Gal(L/F) 𝓟₀) := sorry
  rw [← Equiv.prod_comp e]
  simp [e]
  rw [Fintype.prod_prod_type]

--  have {σ : Gal(L/F)}:= Ideal.coe_smul_primesOver_mk (p := under (𝓞 F) 𝓟) σ 𝓟
  -- have (x : MulAction.orbit Gal(L/F) 𝓟₀) (y : MulAction.stabilizer Gal(L/F) 𝓟₀) :=
  --   congr_arg ((↑) : _ → Ideal (𝓞 L)) <| MulAction.orbitProdStabilizerEquivGroup_apply_smul Gal(L/F) 𝓟₀ x y
  -- have (𝓠) (s) : MulAction.orbitProdStabilizerEquivGroup Gal(L/F) 𝓟₀ (𝓠, s) • 𝓟 = 𝓠.1 := by
  --   rw [← MulAction.orbitProdStabilizerEquivGroup_apply_smul Gal(L/F) 𝓟₀ 𝓠 s]
  --   sorry
  -- simp_rw [this, Finset.prod_pow_eq_pow_sum]
--  have : MulAction.IsPretransitive Gal(L/F) ↑(p₀.primesOver (𝓞 L)) := by
--    convert Ideal.isPretransitive_of_isGaloisGroup _ _

  -- have := MulAction.orbitProdStabilize rEquivGroup_apply_smul


    -- MulAction.orbitProdStabilizerEquivGroup_apply_smul

  sorry

theorem step5 [P.LiesOver 𝒑] [Algebra E L] {Γ : 𝓞 E} (hΓ : GaussSum hbij hζ d ^ m = algebraMap (𝓞 E) (𝓞 L) Γ)
    (P₀ : Ideal (𝓞 E)) [P₀.IsPrime] [P₀.LiesOver 𝒑] (hP₀ : ¬ P₀ ∣ span {(m : 𝓞 E)}) :
    span {Γ} = ∏ τ : Gal(E/ℚ), P₀ * θ τ := sorry

theorem step6 (P₀ : Ideal (𝓞 E)) [P₀.IsPrime] (hP₀ : ¬ P₀ ∣ span {(m : 𝓞 E)}) :
    Submodule.IsPrincipal P₀ := sorry
