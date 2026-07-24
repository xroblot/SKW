module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public import SKW.Stickelberger.valGauss

@[expose] public section

open Ideal NumberField IntermediateField Pointwise IsCyclotomicExtension.Rat

noncomputable section

variable (p f : ℕ) [NeZero (p ^ f - 1)]

local notation3 "𝒑" => span {(p : ℤ)}

variable {p f}

variable {L : Type*} [Field L] [NumberField L] {F K : IntermediateField ℚ L} {P : Ideal (𝓞 K)}

variable (hbij : Function.Bijective (rootsOfUnity.mapQuot (p ^ f - 1) P))

variable {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p) {η : 𝓞 K} (hη : IsPrimitiveRoot η (p ^ f - 1))

variable [P.IsMaximal] (𝓟 : Ideal (𝓞 L)) [hp : Fact (p.Prime)]

local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

variable (m d : ℕ) (hmf : orderOf (p : ZMod m) = f) (hdm : d * m = p ^ f - 1)

variable {E : IntermediateField ℚ L} [IsCyclotomicExtension {m * p} ℚ E] (𝔓 : Ideal (𝓞 E))

variable {k : IntermediateField ℚ L} (𝔭 : Ideal (𝓞 k))

include hη hdm in
theorem smul_gaussSum_eq_gaussSum' [NeZero f] [NeZero m] [Fact (Odd p)] [IsCyclotomicExtension {p} ℚ F]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [IsCyclotomicExtension {p ^ f - 1} ℚ K] [P.LiesOver 𝒑]
    [Algebra F E] [IsScalarTower F E L] (τ : Gal(L/E)) :
    τ • (GaussSum hbij hζ d ^ m) = GaussSum hbij hζ d ^ m := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p * (p ^ f - 1)} ℚ L
  -- fix for merge: convert_to side goal ordering changed; use explicit rfl step
  have hτ : τ • (GaussSum hbij hζ d ^ m) = (τ.restrictScalars F) • (GaussSum hbij hζ d ^ m) := rfl
  rw [hτ, smul_pow', gal_gaussSum_eq_gaussSum hbij hζ hη]
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
            rw [← map_pow, ← pow_mul, ← mul_assoc, hdm, pow_mul, hη.pow_eq_one, one_pow, map_one])
        refine ⟨ε ^ i, ?_⟩
        rw [map_pow _ ε, hi]
      rw [hx, AlgEquiv.smul_def, AlgEquiv.coe_restrictScalars, AlgEquiv.commutes]
    have := congr_arg (· ^ d) <| galLFEquiv_apply_eta p f hη (τ.restrictScalars F)
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
  · rfl

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
    ← MulChar.pow_apply' _ (NeZero.ne m), ← pow_mul, hdm, show teichmuller hbij ^ (p ^ f - 1) = 1 by
        convert pow_orderOf_eq_one (teichmuller hbij)
        exact (orderOf_teichmuller hbij hη).symm,
    MulChar.one_apply this, map_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
variable (E k) in
include 𝓟 hη hdm in
theorem exists_mem_gaussSum_pow_eq [NeZero f] [NeZero m] [Fact (Odd p)] [Algebra F E] [IsScalarTower F E L]
    [P.LiesOver 𝒑] [IsCyclotomicExtension {m} ℚ k] [IsCyclotomicExtension {p} ℚ F] [𝓟.IsPrime]
    [𝓟.LiesOver P]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [IsCyclotomicExtension {p ^ f - 1} ℚ K] :
    ∃ Γ : 𝓞 k, Γ ≠ 0 ∧ GaussSum hbij hζ d ^ m = algebraMap (𝓞 k) (𝓞 L) Γ := by
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {p * (p ^ f - 1)} ℚ L
  suffices ↑(GaussSum hbij hζ d ^ m : 𝓞 L) ∈ k by
    refine ⟨⟨⟨(GaussSum hbij hζ d ^ m : 𝓞 L), this⟩,
      coe_isIntegral_iff.mp <| RingOfIntegers.isIntegral_coe _⟩, ?_, rfl⟩
    rw [← map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 L))]
    exact_mod_cast pow_ne_zero m <| GaussSum_ne_zero hbij hζ hη 𝓟 _
  have : k = E ⊓ K := by
    have : p.Coprime d := (coprime_pow_sub_one p f).symm.of_dvd_right (Dvd.intro m hdm)
    convert isCyclotomicExtension_eq {m} ℚ L k _
    -- fix for merge: convert now leaves typeclass diamond goals, closed by rfl
    convert IsCyclotomicExtension.Rat.gcd_inf (m * p) (p ^ f - 1) E K
    · rw [← hdm, mul_comm d, Nat.gcd_mul_left, this, mul_one]
    all_goals rfl
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

omit [NeZero (p ^ f - 1)] in
include hdm in
theorem ramificationIdx_eq_one [NeZero f] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]
    [𝓟.LiesOver 𝔓] [𝔓.LiesOver 𝒑] [𝔓.IsPrime] [𝓟.IsPrime] :
    ramificationIdx' 𝔓 𝓟 = 1 := by
  have hpq : ¬ p ∣ p ^ f - 1 := (Nat.Prime.coprime_iff_not_dvd hp.out).mp (coprime_pow_sub_one p f).symm
  have hpm : ¬ p ∣ m := hp.out.coprime_iff_not_dvd.mp <|
    (coprime_pow_sub_one p f).symm.of_dvd_right <| Dvd.intro_left d hdm
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 𝔓 𝒑
  have htower := Ideal.ramificationIdx'_algebra_tower' 𝒑 𝔓 𝓟
  rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝒑 𝓟 (by simpa using hp.out.ne_zero),
    @IsCyclotomicExtension.Rat.ramificationIdx_eq (p * (p ^ f - 1)) (p ^ f - 1) p 0 hp L _ _ 𝓟 _ _ _
      (by ring) hpq,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝒑 𝔓 (by simpa using hp.out.ne_zero),
    @IsCyclotomicExtension.Rat.ramificationIdx_eq (m * p) m p 0 hp E _ _ 𝔓 _ _ _
      (by ring) hpm] at htower
  simp at htower
  have hne : p - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hp.out.one_lt
  nlinarith [Nat.pos_of_ne_zero hne]

omit [NeZero (p ^ f - 1)] in
include hdm in
theorem ramificationIdx_eq_sub_one₀ [NeZero f] [NeZero m] [Algebra k E] [𝔓.LiesOver 𝔭] [𝔭.LiesOver 𝒑]
    [𝔓.IsPrime] [IsCyclotomicExtension {m} ℚ k] [𝔭.IsPrime] :
    ramificationIdx' 𝔭 𝔓 = p - 1 := by
  have hpm : ¬ p ∣ m := hp.out.coprime_iff_not_dvd.mp <|
    (coprime_pow_sub_one p f).symm.of_dvd_right <| Dvd.intro_left d hdm
  have : 𝔓.LiesOver 𝒑 := LiesOver.trans 𝔓 𝔭 𝒑
  have htower := Ideal.ramificationIdx'_algebra_tower' 𝒑 𝔭 𝔓
  rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝒑 𝔓 (by simpa using hp.out.ne_zero),
    @IsCyclotomicExtension.Rat.ramificationIdx_eq (m * p) m p 0 hp E _ _ 𝔓 _ _ _
      (by ring) hpm,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝒑 𝔭 (by simpa using hp.out.ne_zero),
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p k 𝔭 hpm,
    one_mul] at htower
  simpa using htower.symm

omit [NeZero (p ^ f - 1)] [IsCyclotomicExtension {m * p} ℚ E] in
include hdm in
theorem ramificationIdx_eq_sub_one [NeZero f] [NeZero m] [𝔭.LiesOver 𝒑]
    [IsCyclotomicExtension {m} ℚ k] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [𝔭.IsPrime]
    [𝓟.IsPrime] [𝓟.LiesOver 𝔭] :
    ramificationIdx' 𝔭 𝓟 = p - 1 := by
  have hpq : ¬ p ∣ p ^ f - 1 := (Nat.Prime.coprime_iff_not_dvd hp.out).mp (coprime_pow_sub_one p f).symm
  have hpm : ¬ p ∣ m := hp.out.coprime_iff_not_dvd.mp <|
    (coprime_pow_sub_one p f).symm.of_dvd_right <| Dvd.intro_left d hdm
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 𝔭 𝒑
  have htower := Ideal.ramificationIdx'_algebra_tower' 𝒑 𝔭 𝓟
  rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝒑 𝓟 (by simpa using hp.out.ne_zero),
    @IsCyclotomicExtension.Rat.ramificationIdx_eq (p * (p ^ f - 1)) (p ^ f - 1) p 0 hp L _ _ 𝓟 _ _ _
      (by ring) hpq,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝒑 𝔭 (by simpa using hp.out.ne_zero),
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p k 𝔭 hpm,
    one_mul] at htower
  simpa using htower.symm

variable (p) in
theorem galEquivZMod_stabilizer' [IsCyclotomicExtension {m} ℚ k] [NeZero m] [𝔭.IsMaximal] [𝔭.LiesOver 𝒑]
    (hp' : p.Coprime m) :
    MulEquiv.mapSubgroup (galEquivZMod m k) (MulAction.stabilizer Gal(k/ℚ) 𝔭) =
      Subgroup.zpowers (ZMod.unitOfCoprime p hp') := galEquivZMod_stabilizer m k p 𝔭 hp'

theorem galEquivZMod_mul_smul_of_zpowers [IsCyclotomicExtension {m} ℚ k] [NeZero m] [𝔭.IsMaximal]
    [𝔭.LiesOver 𝒑] (a : (ZMod m)ˣ) (hp' : p.Coprime m) (b : Subgroup.zpowers (ZMod.unitOfCoprime p hp')) :
    (galEquivZMod m k).symm (a * b) • 𝔭 = (galEquivZMod m k).symm a • 𝔭 := by
  have : ((galEquivZMod m k).symm a • 𝔭).LiesOver 𝒑 := LiesOver.smul _
  have : ((galEquivZMod m k).symm a • 𝔭).IsMaximal := by
    apply (IsPrime.smul _).isMaximal
    rw [← Ideal.zero_eq_bot, smul_ne_zero_iff_ne]
    exact NeZero.ne 𝔭
  rw [mul_comm, map_mul, ← smul_eq_mul, smul_assoc, ← MulAction.mem_stabilizer_iff,
    ← Subgroup.mem_map_equiv, ← MulEquiv.coe_mapSubgroup, galEquivZMod_stabilizer' p]
  exact b.prop

include hη hdm in
theorem mul_valGauss_eq_mul_sum [NeZero f] [NeZero m] [NeZero d] [𝓟.LiesOver P] [P.LiesOver 𝒑]
    [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]
    [IsCyclotomicExtension {p ^ f - 1} ℚ K] [Fact (Odd p)] [𝓟.IsPrime] (a : ℕ) (ha : d * a ≤ p ^ f - 2) :
    m * (valGauss hbij hζ 𝓟 (d * a : ℕ)) = (p - 1 : ℕ) * ∑ i ∈ Finset.range f, (a * p ^ i % m) := by
  rw [← Nat.cast_mul, ← ENat.natCast_toNat (valGauss_ne_top₀' hbij hζ hη 𝓟 _), ← Nat.cast_mul,
    Nat.cast_inj]
  qify
  rw [← Nat.cast_mul d, valGauss_toNat_eq_sum_digits hbij hζ hη _ _ ha,
    ← Nat.sub_one_mul_sum_fract_div_eq_digits_sum hp.out.one_lt (l := f) ha]
  simp_rw [← hdm, Nat.cast_mul, div_mul_eq_div_div, mul_div_assoc _ _ (d :ℚ), ← mul_div_assoc (d : ℚ),
    mul_div_cancel_left₀ (a : ℚ) (a := ↑d) (by simpa using NeZero.ne _)]
  rw [← mul_assoc, mul_comm (m : ℚ), mul_assoc, Finset.mul_sum, Nat.cast_sub hp.out.one_le, Nat.cast_one]
  congr with j
  rw [← Nat.cast_pow, ← Nat.cast_mul, ← Rat.intCast_natCast, ← Rat.intCast_natCast,
    mul_fract_div_eq_mod _ _ (Int.natCast_pos.mpr (NeZero.pos m)), Nat.cast_mul, Nat.cast_pow, mul_comm]

include hη hdm in
theorem gaFEquiv_symm_smul_algebraMap_eq [NeZero f] [NeZero m] [IsCyclotomicExtension {m} ℚ k]
    [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] (a : (ZMod m)ˣ) (b : (ZMod (p ^ f - 1))ˣ) (x : 𝓞 k)
    (hb : b.val.cast = a.val) :
    (galFEquiv p f (F := F) K).symm b • (algebraMap (𝓞 k) (𝓞 L)) x =
      (algebraMap (𝓞 k) (𝓞 L)) ((galEquivZMod m k).symm a • x) := by
  rw [smul_eq_galRestrict_apply (𝓞 F), smul_eq_galRestrict_apply ℤ]
  suffices (((galRestrict (𝓞 F) (F) L (𝓞 L))
      ((galFEquiv p f K).symm b)).toAlgHom.restrictScalars ℤ).comp
        (IsScalarTower.toAlgHom ℤ (𝓞 k) (𝓞 L)) = (IsScalarTower.toAlgHom ℤ (𝓞 k) (𝓞 L)).comp
          (((galRestrict ℤ ℚ (↥k) (𝓞 ↥k)) ((galEquivZMod m ↥k).symm a)).toAlgHom.restrictScalars ℤ) by
    exact AlgHom.congr_fun this x
  let ε : k := IsCyclotomicExtension.zeta m ℚ k
  have hε : IsPrimitiveRoot ε m := IsCyclotomicExtension.zeta_spec m ℚ k
  apply AlgHom.ext_of_adjoin_eq_top (adjoin_singleton_eq_top hε)
  simp only [Set.eqOn_singleton, AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgEquiv.coe_toAlgHom,
    IsScalarTower.coe_toAlgHom', Function.comp_apply, ← smul_eq_galRestrict_apply (𝓞 F),
    ← smul_eq_galRestrict_apply ℤ]
  rw [galEquivZMod_smul_of_pow_eq m, MulEquiv.apply_symm_apply, galLFEquiv_apply_of_pow_eq_one p f hη,
    MulEquiv.apply_symm_apply, ← map_pow, (FaithfulSMul.algebraMap_injective _ _).eq_iff]
  · have : a.val.val % m = b.val.val % m := by simp [← hb, ← ZMod.natCast_val]
    rw [← pow_mod_orderOf _ b.val.val, ← pow_mod_orderOf _ a.val.val,
       ← hε.toInteger_isPrimitiveRoot.eq_orderOf, this]
  · rw [← map_pow, map_eq_one_iff _ (FaithfulSMul.algebraMap_injective _ _ ),
      hε.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd]
    exact Dvd.intro_left d hdm
  · exact hε.toInteger_isPrimitiveRoot.pow_eq_one

include hη 𝓟 hdm in
theorem emultiplicity_galEquivZMod_symm_smul_gaussSum [IsCyclotomicExtension {m} ℚ k]
    [IsCyclotomicExtension {p ^ f - 1} ℚ K] [NeZero m] [NeZero d]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [IsCyclotomicExtension {p} ℚ F]
    [NeZero f] [𝓟.IsPrime] [NeZero 𝓟] [Fact (Odd p)] [𝓟.LiesOver P]  [𝓟.LiesOver 𝔭] [P.LiesOver 𝒑]
    [𝔭.LiesOver 𝒑] (a : (ZMod m)ˣ) {Γ : 𝓞 k} (hΓ₀ : Γ ≠ 0)
    (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 k) (𝓞 L) Γ) :
    emultiplicity (((galEquivZMod m k).symm a⁻¹) • 𝔭) (span {Γ}) =
      ∑ j ∈ Finset.range f, (a.val.val * p ^ j) % m := by
  obtain ⟨b, hb⟩ := ZMod.unitsMap_surjective (Dvd.intro_left d hdm) a
  replace hb := congr_arg Units.val hb
  rw [ZMod.unitsMap_val] at hb
  let σ := (galFEquiv p f (F := F) K).symm b⁻¹
  have : 𝔭.IsPrime := isPrime_of_liesOver 𝓟 𝔭
  have h𝓟₀ : σ • 𝓟 ≠ ⊥ := by simpa using NeZero.ne 𝓟
  have h𝓟 : Prime (σ • 𝓟) := Ideal.prime_of_isPrime h𝓟₀ (IsPrime.smul σ)
  have h𝓟' : Irreducible (σ • 𝓟) := UniqueFactorizationMonoid.irreducible_iff_prime.mpr h𝓟
  have hmain := congr_arg ((d : ℕ∞) * ·) <| congr_arg (emultiplicity (σ • 𝓟) ·)
    <| congr_arg (Ideal.span {·}) <| hΓ
  have : ↑(d * (galFEquiv p f K σ⁻¹).val.val : ℕ) ≡
      ↑(d * a.val.val : ℕ) [ZMOD (p ^ f - 1 : ℕ)] := by
    unfold σ
    nth_rewrite 1 [← hdm]
    rw [← map_inv, inv_inv, MulEquiv.apply_symm_apply, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Int.ModEq.mul_left_cancel_iff', Int.ModEq, Int.ofNat_mod_ofNat, Int.ofNat_mod_ofNat,
      Nat.cast_inj, ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, hb, ZMod.natCast_zmod_val]
    rw [Int.natCast_ne_zero]
    exact NeZero.ne _
  rw [← Ideal.span_singleton_pow, emultiplicity_pow h𝓟, emultiplicity_smul_GaussSum hbij hζ hη,
    ← Set.image_singleton, ← map_span,
    ← Ideal.IsDedekindDomain.ramificationIdx_mul_emultiplicity_under_eq h𝓟' h𝓟₀, ← Nat.cast_mul,
    valGauss_periodic' hbij hζ hη _ _ _ this, mul_valGauss_eq_mul_sum hbij hζ hη _ m _ hdm] at hmain
  have : under (𝓞 k) (σ • 𝓟) = ((galEquivZMod m k).symm a⁻¹) • 𝔭 := by
    ext
    unfold σ
    rw [over_def 𝓟 𝔭, mem_pointwise_smul_iff_inv_smul_mem, map_inv, map_inv, inv_inv, under_def, under_def,
      Ideal.mem_comap, Ideal.mem_comap, mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
      gaFEquiv_symm_smul_algebraMap_eq hη m d hdm _ _ _ hb]
  rw [this] at hmain
  have : (((galEquivZMod m k).symm a⁻¹ • 𝔭).ramificationIdx' (σ • 𝓟)) = p - 1 := by
    have := (liesOver_iff _ _).mpr this.symm
    rw [ramificationIdx_eq_sub_one _ m d hdm]
  rw [this, FiniteMultiplicity.emultiplicity_eq_multiplicity, ← Nat.cast_mul, ← Nat.cast_mul,
    ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_inj] at hmain
  have : p - 1 ≠ 0 := by
    rw [Nat.sub_ne_zero_iff_lt]
    exact hp.out.one_lt
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity, Nat.cast_inj, ← mul_right_inj' this,
    ← mul_right_inj' (NeZero.ne d), ← hmain]
  · refine IsDedekindDomain.finiteMulticity ?_ ?_
    · simpa using IsPrime.ne_top'
    · simpa using hΓ₀
  · refine IsDedekindDomain.finiteMulticity ?_ ?_
    · simpa using IsPrime.ne_top'
    · simpa using hΓ₀
  · have := (Nat.mul_lt_mul_left (NeZero.pos d)).mpr <| ZMod.val_lt a.val
    rw [hdm] at this
    exact Nat.le_sub_one_of_lt this

variable [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p ^ f - 1} ℚ K] [NeZero f] [𝓟.IsPrime]

include hη 𝓟 in
theorem emultplicity_gaussSum_eq_zero [P.LiesOver 𝒑] {𝔭 : Ideal (𝓞 k)} [NeZero 𝓟]
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
  apply IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
  exact hP₀.ne_zero

theorem emultiplicity_galEquivZMod_symm_smul [IsCyclotomicExtension {m} ℚ k] [NeZero m] [𝔭.IsPrime]
    [NeZero 𝔭] {𝔮 : Ideal (𝓞 k)} (hq : Prime 𝔮) :
    emultiplicity 𝔮 (∏ a, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val) =
      ∑ a, if (galEquivZMod m k).symm a • 𝔮 = 𝔭 then a.val.val else 0 := by
  classical
  have {x : (ZMod m)ˣ} : Prime (((galEquivZMod m k).symm x)⁻¹ • 𝔭) := by
    refine prime_of_isPrime ?_ (IsPrime.smul _)
    · rw [← Ideal.zero_eq_bot, smul_ne_zero_iff_ne]
      exact NeZero.ne _
  rw [Finset.emultiplicity_prod hq]
  simp_rw [emultiplicity_pow hq, Prime.emultiplicity_prime hq this, associated_iff_eq,
    smul_eq_iff_eq_inv_smul, mul_ite, mul_one, mul_zero, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

omit [NeZero (p ^ f - 1)] hp [NeZero f] in
include hmf in
theorem sum_with_mul_inv_mem_eq_sum_range [NeZero m] (b : (ZMod m)ˣ) (hp' : p.Coprime m)
    (g : (ZMod m) → ℕ) :
    ∑ a with a * b⁻¹ ∈ Finset.image (fun j ↦ ZMod.unitOfCoprime p hp' ^ j)
      (Finset.range f), g a = ∑ j ∈ Finset.range f, g (b * (ZMod.unitOfCoprime p hp') ^ j) := by
  classical
  rw [eq_comm, Finset.sum_of_injOn fun j ↦ b * (ZMod.unitOfCoprime p hp') ^ j]
  · have : orderOf (ZMod.unitOfCoprime p hp') = f := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime]
      exact hmf
    intro i hi j hj h
    rwa [mul_right_inj, pow_inj_mod, this, Nat.mod_eq_of_lt (Finset.mem_range.mp hj),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hi)] at h
  · intro j hj
    simpa using ⟨j, List.mem_range.mp hj, rfl⟩
  · intro a h₁ h₂
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.coe_range, Set.mem_image, Set.mem_Iio, not_exists, not_and] at h₁ h₂
    obtain ⟨j, hj, hj'⟩ := h₁
    have := h₂ j hj
    rw [hj', mul_mul_inv_cancel'_right] at this
    exact False.elim (Ne.irrefl this)
  · intro _ _
    simp

omit [𝓟.IsPrime] in
include hη hdm hmf in
theorem GaussSum_factorization [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]
    [IsCyclotomicExtension {m} ℚ k] [NeZero m] [NeZero d] [NeZero 𝓟] [𝓟.IsPrime]
    [Fact (Odd p)] [𝓟.LiesOver P] [P.LiesOver 𝒑] [𝔭.IsMaximal] [𝓟.LiesOver 𝔭] [𝔭.LiesOver 𝒑]
    (Γ : 𝓞 k) (hΓ₀ : Γ ≠ 0)
    (hΓ : (GaussSum hbij hζ d) ^ m = algebraMap (𝓞 k) (𝓞 L) Γ) :
    span {Γ} = ∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val := by
  rw [UniqueFactorizationMonoid.eq_iff_emultiplicity_eq]
  intro 𝔮 hQ₀
  have : 𝔮.IsMaximal := (isPrime_of_prime hQ₀).isMaximal hQ₀.ne_zero
  by_cases hP₀' : 𝔮.LiesOver 𝒑
  · have := IsCyclotomicExtension.isGalois {m} ℚ k
    have hp' : p.Coprime m := (coprime_pow_sub_one p f).symm.of_dvd_right <| Dvd.intro_left d hdm
    obtain ⟨σ, rfl⟩ : ∃ σ : Gal(k/ℚ), 𝔮 = σ⁻¹ • 𝔭 := by
      obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝒑 𝔭 𝔮 Gal(k/ℚ)
      exact ⟨σ⁻¹, by rw [inv_inv]⟩
    rw [emultiplicity_galEquivZMod_symm_smul _ _ hQ₀]
    obtain ⟨b, hb⟩ : ∃ b, σ⁻¹ = (galEquivZMod m k).symm b⁻¹ :=
      ⟨galEquivZMod m k σ, by rw [map_inv, MulEquiv.symm_apply_apply]⟩
    rw [hb, emultiplicity_galEquivZMod_symm_smul_gaussSum hbij hζ hη 𝓟 m d hdm 𝔭 _ hΓ₀ hΓ]
    simp_rw [smul_smul, ← map_mul, ← MulAction.mem_stabilizer_iff]
    simp_rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs =>
      enter [1, 1, 1, x]
      rw [← Subgroup.mem_map_equiv, ← MulEquiv.coe_mapSubgroup, galEquivZMod_stabilizer' p m 𝔭 hp']
    have t₁ : orderOf (ZMod.unitOfCoprime p hp') = f := by
      rwa [← orderOf_units, ZMod.coe_unitOfCoprime]
    have t₂ : IsOfFinOrder (ZMod.unitOfCoprime p hp') := by
      exact isOfFinOrder_of_finite (ZMod.unitOfCoprime p hp')
    simp_rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf t₂, t₁,
      sum_with_mul_inv_mem_eq_sum_range m hmf]
    simp [← ZMod.val_natCast]
  · obtain ⟨𝓠, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔮
    have {σ : Gal(k/ℚ)} : σ • 𝔮 ≠ 𝔭 := by
      contrapose! hP₀'
      rw [(smul_eq_iff_eq_inv_smul _).mp hP₀']
      exact LiesOver.smul σ⁻¹
    rw [emultplicity_gaussSum_eq_zero hbij hζ hη 𝓠 m d hΓ hQ₀ hP₀', emultiplicity_galEquivZMod_symm_smul m 𝔭 hQ₀, Nat.cast_sum]
    simp [if_neg this]
