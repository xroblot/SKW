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

variable [IsCyclotomicExtension {p} ℚ F]

local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

variable (m d : ℕ) (hm : orderOf (p : ZMod m) = f) (hmd : p ^ f - 1 = m * d)

variable {E : Type*} [Field E] [NumberField E] [IsCyclotomicExtension {m * p} ℚ E]

variable (tP : Ideal (𝓞 E))

variable {E₀ : Type*} [Field E₀] [NumberField E₀] -- [IsCyclotomicExtension {m} ℚ E₀]

variable (tP₀ : Ideal (𝓞 E₀))

theorem lemma34 [P.LiesOver 𝒑] [Algebra E L] (τ : Gal(L/E)) :
    τ • (GaussSum hbij hζ d ^ m) = GaussSum hbij hζ d ^ m := sorry

theorem lemma35 [P.LiesOver 𝒑] (τ : Gal(L/K)) {e : ℕ}
    (h : τ • algebraMap (𝓞 F) (𝓞 L) ζ = algebraMap (𝓞 F) (𝓞 L) ζ ^ e) :
    τ • GaussSum hbij hζ d = ((teichmuller hbij ^ (-(d : ℤ))) e)  • GaussSum hbij hζ d := sorry

theorem lemme36 [P.LiesOver 𝒑] (τ : Gal(L/K)) :
    τ • (GaussSum hbij hζ d) ^ m = GaussSum hbij hζ d ^ m := sorry

theorem lemma37 [Algebra E₀ L] [P.LiesOver 𝒑] :
    ∃ Γ : 𝓞 E₀, (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 E₀) (𝓞 L) Γ := sorry

theorem lemma38 [Algebra E L] [𝓟.LiesOver 𝒑] [𝓟.LiesOver tP] :
    ramificationIdx tP 𝓟 = 1 := sorry

theorem lemma39 [Algebra E₀ E] [tP.LiesOver tP₀] [tP.LiesOver 𝒑] :
    ramificationIdx tP₀ tP = p - 1 := sorry

theorem lemma40 [IsCyclotomicExtension {m} ℚ E₀] [NeZero m] (a : (ZMod m)ˣ) (hp' : p.Coprime m)
    (b : Subgroup.zpowers (ZMod.unitOfCoprime p hp')) :
    (galEquivZMod m E₀).symm (a * b) • tP₀ = (galEquivZMod m E₀).symm a • tP₀ := sorry

def mθ (a : (ZMod m)) : ℕ := a.val - m * ⌊a.val / m⌋₊

theorem lemma41 [IsCyclotomicExtension {m} ℚ E₀] [NeZero m] [P.LiesOver 𝒑] [Algebra E₀ L]
    (a : (ZMod m)ˣ) {Γ : 𝓞 E₀}
    (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 E₀) (𝓞 L) Γ) :
    emultiplicity (((galEquivZMod m E₀).symm a⁻¹) • tP₀) (span {Γ}) =
      ∑ j ∈ Finset.range f, mθ m (a.val.val * p ^ j) := sorry

theorem lemma42 [IsCyclotomicExtension {m} ℚ E₀] [NeZero m] (a : (ZMod m)ˣ) :
    emultiplicity (((galEquivZMod m E₀).symm a)⁻¹ • tP₀)
      (∏ a, (((galEquivZMod m E₀).symm a)⁻¹ • tP₀) ^ (mθ m a)) =
        ∑ i ∈ Finset.range f, mθ m (a.val.val * p ^ i) := sorry

variable [IsCyclotomicExtension {p ^ f - 1} ℚ K] [NeZero f] [𝓟.IsPrime]

include hη 𝓟 in
theorem lemma43_1 [P.LiesOver 𝒑] [Algebra E₀ L] {P₀ : Ideal (𝓞 E₀)} [NeZero 𝓟]
    [𝓟.LiesOver P₀] {Γ : 𝓞 E₀} (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 E₀) (𝓞 L) Γ)
    (hP₀ : Prime P₀) (hP₀' : ¬ P₀.LiesOver 𝒑) :
    emultiplicity P₀ (span {Γ}) = 0 := by
  have h𝓟 : Prime 𝓟 := (prime_iff_isPrime (NeZero.ne _)).mpr inferInstance
  have : emultiplicity 𝓟 (span {GaussSum hbij hζ d ^ m}) = 0 := by
    have : ¬ 𝓟.LiesOver 𝒑 := by
      contrapose! hP₀'
      exact LiesOver.tower_bot 𝓟 P₀ 𝒑
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

theorem lemma43_2 [IsCyclotomicExtension {m} ℚ E₀] [NeZero m] {P₀ : Ideal (𝓞 E₀)} (hP₀ : Prime P₀) :
    emultiplicity P₀ (∏ a, (((galEquivZMod m E₀).symm a)⁻¹ • tP₀) ^ (mθ m a)) =
      ∑ a, if (galEquivZMod m E₀).symm a • P₀ = tP₀ then mθ m a else 0 := sorry

variable (K) in
theorem lemma43_3 [Algebra E₀ L] (σ : Gal(E₀/ℚ)) :
    ∃ τ : Gal(L/K), σ • tP₀ = comap (algebraMap (𝓞 E₀) (𝓞 L)) (τ • 𝓟) := sorry

theorem lemma43_4 [NeZero m] (b : (ZMod m)ˣ) (hp' : p.Coprime m) (g : (ZMod m)ˣ → ℕ) :
    ∑ a with a * b⁻¹ ∈ Finset.image (fun x ↦ ZMod.unitOfCoprime p hp' ^ x)
      (Finset.range f), g a = ∑ j ∈ Finset.range f, g (b * (ZMod.unitOfCoprime p hp') ^ j) := sorry

include K 𝓟 hη in
theorem lemma43 [IsCyclotomicExtension {m} ℚ E₀] [NeZero m] [NeZero 𝓟] [P.LiesOver 𝒑]
    [Algebra E₀ L] [𝓟.LiesOver tP₀] (Γ : 𝓞 E₀)
    (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 E₀) (𝓞 L) Γ) :
    span {Γ} = ∏ a, (((galEquivZMod m E₀).symm a)⁻¹ • tP₀) ^ mθ m a := by
  rw [UniqueFactorizationMonoid.eq_iff_emultiplicity_eq]
  intro P₀ hP₀
  by_cases hP₀' : P₀.LiesOver 𝒑
  · have hp' : p.Coprime m := sorry
    obtain ⟨σ, rfl⟩ : ∃ σ : Gal(E₀/ℚ), P₀ = σ⁻¹ • tP₀ := sorry
    rw [lemma43_2 _ _ hP₀]
    obtain ⟨b, hb⟩ : ∃ b, σ⁻¹ = (galEquivZMod m E₀).symm b⁻¹ := sorry
    rw [hb, lemma41 hbij hζ m d tP₀ _ hΓ]
    simp_rw [smul_smul, ← MulAction.mem_stabilizer_iff, ← map_mul]
    conv_rhs =>
      enter [1, 2, x, 1]
      rw [← Subgroup.mem_map_equiv, MulEquiv.toMonoidHom_eq_coe]
    have t₀ : Subgroup.map (↑(galEquivZMod m E₀)) (MulAction.stabilizer Gal(E₀/ℚ) tP₀) =
      Subgroup.zpowers (ZMod.unitOfCoprime p hp') := sorry
    have t₁ : orderOf (ZMod.unitOfCoprime p hp') = f := sorry
    have t₂ : IsOfFinOrder (ZMod.unitOfCoprime p hp') := sorry
    simp_rw [t₀, IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf t₂, t₁]
    simp_rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, lemma43_4]
    simp
  · have : 𝓟.LiesOver P₀ := sorry
    have {σ : Gal(E₀/ℚ)} : σ • P₀ ≠ tP₀ := sorry
    rw [lemma43_1 hbij hζ hη 𝓟 m d hΓ hP₀ hP₀', lemma43_2 m tP₀ hP₀, Nat.cast_sum]
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
