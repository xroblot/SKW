module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.Ideal.IsPrincipal

public import SKW.Stickelberger.Factorization
public import SKW.Prereqs.ClassGroup
public import SKW.Prereqs.ClassGroupCoprime
public import SKW.Prereqs.IdealNorm

@[expose] public section

open Ideal NumberField IntermediateField Pointwise IsCyclotomicExtension.Rat

variable (m : ℕ) (k : Type*) [Field k] [NumberField k] [NeZero m]
  [IsCyclotomicExtension {m} ℚ k] (p : ℕ) [hp : Fact (p.Prime)] [Fact (Odd p)] (hp' : ¬ p ∣ m)
  (𝔭 : Ideal (𝓞 k)) [𝔭.IsMaximal] [𝔭.LiesOver (span {(p : ℤ)})]

attribute [local instance] Ideal.Quotient.field

set_option backward.isDefEq.respectTransparency false in
theorem Stickelberger_aux (f d : ℕ) [NeZero f] [NeZero d] [NeZero (p * (p ^ f - 1))] [NeZero (p ^ f - 1)]
    (hdm : d * m = p ^ f - 1) (hf : orderOf (p : ZMod m) = f) (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    Submodule.IsPrincipal (∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val) := by
  classical
  let ξ := IsCyclotomicExtension.zeta (p * (p ^ f - 1)) ℚ L
  have hξ := IsCyclotomicExtension.zeta_spec (p * (p ^ f - 1)) ℚ L
  let η₀ := ξ ^ p
  have hη₀ : IsPrimitiveRoot η₀ (p ^ f - 1) := hξ.pow (NeZero.pos _) rfl
  let K := ℚ⟮η₀⟯
  have : IsPrimitiveRoot (AdjoinSimple.gen ℚ η₀) (p ^ f - 1) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hη₀
  let η := this.toInteger
  have hη : IsPrimitiveRoot η (p ^ f - 1) := this.toInteger_isPrimitiveRoot
  have : IsCyclotomicExtension {p ^ f - 1} ℚ K := hη₀.intermediateField_adjoin_isCyclotomicExtension ℚ
  let ζ₀ := ξ ^ (p ^ f - 1)
  have hζ₀ : IsPrimitiveRoot ζ₀ p := hξ.pow (NeZero.pos _) (by rw [mul_comm])
  let F := ℚ⟮ζ₀⟯
  have : IsPrimitiveRoot (AdjoinSimple.gen ℚ ζ₀) p := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₀
  let ζ := this.toInteger
  have hζ : IsPrimitiveRoot ζ p := this.toInteger_isPrimitiveRoot
  have : IsCyclotomicExtension {p} ℚ F := hζ₀.intermediateField_adjoin_isCyclotomicExtension ℚ
  let E := ℚ⟮ξ ^ d⟯
  have : IsCyclotomicExtension {m * p} ℚ E := by
    refine IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension ℚ ?_
    exact hξ.pow (NeZero.pos _) (by rw [← mul_assoc, hdm, mul_comm])
  let : Algebra F E :=
    (inclusion (IsCyclotomicExtension.le_of_dvd p (m * p) _ _ (dvd_mul_left p m))).toRingHom.toAlgebra
  have : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  let k₀ := ℚ⟮ξ ^ (p * d)⟯
  have : IsCyclotomicExtension {m} ℚ k₀ := by
    refine IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension ℚ ?_
    exact hξ.pow (NeZero.pos _) (by rw [mul_assoc, hdm])
  let e := RingOfIntegers.mapRingEquiv <| (IsCyclotomicExtension.algEquiv {m} ℚ k₀ k).toRingEquiv
  set 𝔭₀ := Ideal.map e.symm 𝔭 with def_p₀
  have : 𝔭₀.IsMaximal := map_isMaximal_of_equiv e.symm
  have : 𝔭₀.LiesOver (span {(p : ℤ)}) := map_equiv_liesOver 𝔭 (span {(p : ℤ)}) (e.toIntAlgEquiv).symm
  obtain ⟨𝓟, h𝓟, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔭₀
  let P := under (𝓞 K) 𝓟
  have : 𝓟.LiesOver (span {(p : ℤ)}) := LiesOver.trans 𝓟 𝔭₀ _
  have : P.LiesOver (span {(p : ℤ)}) := LiesOver.tower_bot 𝓟 P _
  have : P.IsMaximal := IsMaximal.under (𝓞 K) 𝓟
  have hbij : Function.Bijective (rootsOfUnity.mapQuot (p ^ f - 1) P) := by
    change Function.Bijective <| rootsOfUnityMapQuot P (p ^ f - 1)
    have hNP : absNorm P = p ^ f := by
      rw [absNorm_eq_pow_inertiaDeg' P hp.out, Ideal.inertiaDeg'_eq_inertiaDeg, inertia_deg_eq p f]
    have : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)
    have : Fintype (rootsOfUnity (p ^ f - 1) (𝓞 K)) := sorry
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · apply rootsOfUnityMapQuot_injective
      · rw [hNP]
        exact ne_of_gt <|  Nat.lt_of_add_left_lt <| three_le_p_pow p f
      · rw [hNP]
        exact Nat.Coprime.pow_left _ (coprime_pow_sub_one p f).symm
    · rw [← Nat.card_eq_fintype_card, IsPrimitiveRoot.card_rootsOfUnity hη,
        Fintype.card_units (𝓞 K ⧸ P), ← Nat.card_eq_fintype_card, ← absNorm_eq_card, hNP]
  obtain ⟨Γ, hΓ₀, hΓ⟩ := exists_mem_gaussSum_pow_eq hbij hζ hη 𝓟 m d hdm E k₀
  refine ⟨e Γ, ?_⟩
  simp_rw [Ideal.submodule_span_eq, ← Set.image_singleton, ← map_span,
    GaussSum_factorization hbij hζ hη 𝓟 m d hf hdm 𝔭₀ _ hΓ₀ hΓ, ← mapHom_apply, map_prod, mapHom_apply]
  have (a : (ZMod m)ˣ) : ((galEquivZMod m k).symm a)⁻¹ • 𝔭 =
        Ideal.map e (((galEquivZMod m ↥k₀).symm a)⁻¹ • 𝔭₀) := by
    ext x
    rw [← comap_symm e, pointwise_smul_eq_comap 𝔭₀, def_p₀, map_symm, mem_comap, mem_comap, mem_comap]
    rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_symm_apply, inv_inv]
    rw [mem_inv_pointwise_smul_iff]
    change _ ↔ e.toRingHom _ ∈ _
    rw [IsCyclotomicExtension.Rat.ringHom_galEquivZMod_smul (by exact e.injective),
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
  simp_rw [this, Ideal.map_pow]

include hp' in
theorem Stickelberger'' :
    Submodule.IsPrincipal (∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • 𝔭) ^ a.val.val) := by
  let f := orderOf (p : ZMod m)
  have : NeZero f := ⟨orderOf_ne_zero_iff.mpr <|
      IsUnit.isOfFinOrder <| (ZMod.isUnit_iff_coprime p m).mpr <| hp.out.coprime_iff_not_dvd.mpr hp'⟩
  let d := (p ^ f - 1) / m
  have hdm : d * m = p ^ f - 1 := by
    have : m ∣ p ^ f - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub NeZero.one_le, Nat.cast_one, sub_eq_zero, Nat.cast_pow]
      exact pow_orderOf_eq_one _
    rw [mul_comm, Nat.mul_div_eq_iff_dvd.mpr this]
  have hpf : NeZero (p ^ f - 1) :=
    ⟨ne_of_gt <| Nat.sub_pos_iff_lt.mpr <| Nat.lt_of_add_left_lt (three_le_p_pow p f)⟩
  have : NeZero d := ⟨by
    by_contra! h
    rw [← hdm, h, zero_mul] at hpf
    exact neZero_zero_iff_false.mp hpf⟩
  obtain ⟨ξ₀, hξ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure k) (p * (p ^ f - 1))
  have : NumberField ℚ⟮ξ₀⟯ := {
    to_finiteDimensional := adjoin.finiteDimensional <| hξ₀.isIntegral' (NeZero.pos _) }
  have : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ ℚ⟮ξ₀⟯ :=
    hξ₀.adjoinSimple_isCyclotomicExtension _ ℚ (AlgebraicClosure k)
  exact Stickelberger_aux m k p 𝔭 f d hdm rfl ℚ⟮ξ₀⟯

theorem Stickelberger' (I : Ideal (𝓞 k)) (hI₁ : Odd I.absNorm) (hI₂ : m.gcd I.absNorm = 1) :
    Submodule.IsPrincipal (∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • I) ^ a.val.val) := by
  have hI : I ≠ ⊥ := by
    contrapose! hI₁
    simp [hI₁]
  rw [← Ideal.mem_isPrincipalSubmonoid_iff, ← Ideal.prod_normalizedFactors_eq_self hI]
  simp_rw  (config := {singlePass := true}) [← smul_pow', ← Multiset.map_id', ← Multiset.prod_map_pow]
  simp_rw [pointwise_smul_def, ← mapHom_apply, map_multiset_prod, Multiset.map_map]
  rw [← Multiset.prod_map_prod]
  refine Submonoid.multiset_prod_mem _ _ (fun f hf ↦ mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hf₀ : f = 0
  · simpa [hf₀] using! bot_isPrincipal
  rw [← Subtype.coe_mk f (mem_nonZeroDivisors_of_ne_zero hf₀)]
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hf
  obtain ⟨hP₁, hP₂⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mp hP
  let p := (under ℤ P).absNorm
  have hI₃ : p ∣ absNorm I := (Int.absNorm_under_dvd_absNorm P).trans <| map_dvd absNorm hP₂
  have : P.IsMaximal := (isPrime_of_prime hP₁).isMaximal <| Prime.ne_zero hP₁
  have hp : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
  have : Fact (Odd p) := ⟨by
    contrapose! hI₁
    rw [Nat.not_odd_iff_even] at hI₁ ⊢
    exact hI₁.trans_dvd hI₃⟩
  simp only [Function.comp_apply, mapHom_apply, map_pow, mem_isPrincipalSubmonoid_iff]
  refine Stickelberger'' m k p ?_ P
  contrapose! hI₂
  exact Nat.not_coprime_of_dvd_of_dvd hp.out.one_lt hI₂ hI₃

theorem Stickelberger (C : ClassGroup (𝓞 k)) :
    ∏ a : (ZMod m)ˣ, (((galEquivZMod m k).symm a)⁻¹ • C) ^ a.val.val = 1 := by
  obtain ⟨⟨I, hI⟩, rfl, hI'⟩ := ClassGroup.exists_mk0_eq_and_isCoprime C
    (J := span {(2*m : 𝓞 k)}) (by simpa using NeZero.ne m)
  simp_rw [ClassGroup.smul_mk0, ← map_pow, ← map_prod]
  rw [ClassGroup.mk0_eq_one_iff]
  simp only [SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, nonZeroDivisors.val_smul]
  have hcop : Nat.Coprime (Ideal.absNorm I) (2 * m) :=
    Ideal.coprime_absNorm_of_isCoprime_span (by exact_mod_cast hI')
  apply Stickelberger'
  · exact Nat.coprime_two_right.mp (hcop.coprime_dvd_right (dvd_mul_right 2 m))
  · exact (hcop.coprime_dvd_right (dvd_mul_left m 2)).symm
