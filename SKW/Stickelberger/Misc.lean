module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.NumberTheory
public import SKW.Stickelberger.Teichmuller

set_option linter.style.header false

/-!
# Auxiliary results for the Stickelberger development

The results gathered here have nothing to do with Gauss sums: elementary estimates on `p ^ f - 1`,
the characteristic and the inertia degree of the residue field at a prime above `p`, ramification
in the cyclotomic tower, and the identification of the Galois group of `L` over the `p`-th
cyclotomic subfield `F` with the units of `ZMod (p ^ f - 1)`.
-/

@[expose] public section

noncomputable section

open Ideal NumberField IntermediateField

section Misc

variable (p f : ℕ)

theorem three_le_p_pow [NeZero f] [hp : Fact (p.Prime)] [hp' : Fact (Odd p)] : 3 ≤ p ^ f := by
  refine le_trans (Nat.le_pow (NeZero.pos f)) ?_
  exact (Nat.pow_le_pow_iff_left (NeZero.ne f)).mpr <| (Nat.Prime.odd_iff hp.out).mp hp'.out

theorem coprime_pow_sub_one [NeZero f] [Fact (p.Prime)] : (p ^ f - 1).Coprime p := by
  rw [← Nat.coprime_pow_right_iff (NeZero.pos f), Nat.coprime_self_sub_left NeZero.one_le]
  exact Nat.gcd_one_left _

variable [NeZero (p ^ f - 1)]

theorem not_dvd_pow_self_sub_one [hp : Fact (p.Prime)] : ¬ p ∣ p ^ f - 1 := by
  rw [Nat.dvd_sub_iff_right NeZero.one_le (p.div_pow_of_pos f _), Nat.dvd_one]
  · exact hp.out.ne_one
  · by_contra! h
    aesop

end Misc

section Algebra

variable {p f : ℕ}

variable [NeZero (p ^ f - 1)]

variable {L : Type*} [Field L] -- [NumberField L]
variable {K : Type*} [Field K] {P : Ideal (𝓞 K)} [P.HasTeichmullerLift (p ^ f - 1)]

variable {F : Type*} [Field F] {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p)
  --- [IsCyclotomicExtension {p} ℚ F]
  -- {η : 𝓞 K} (hη : IsPrimitiveRoot η (p ^ f - 1)) [IsCyclotomicExtension {p ^ f - 1} ℚ K]

local notation3 "𝒑" => span {(p : ℤ)}

-- variable (𝓟 : Ideal (𝓞 L))

theorem ringChar_quotient_eq [hP : P.LiesOver 𝒑] : ringChar (𝓞 K ⧸ P) = p := by
  have := Ideal.ringChar_quot P
  rwa [← (liesOver_iff _ _).mp hP, absNorm_eq_card, Int.card_ideal_quot] at this

variable [P.IsMaximal]

-- local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

variable [hp : Fact (p.Prime)] (𝓟 : Ideal (𝓞 L)) [𝓟.IsPrime]

-- local instance : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite _

-- local instance [P.LiesOver 𝒑] : ExpChar (𝓞 K ⧸ P) p :=
--  have : CharP (𝓞 K ⧸ P) p := ringChar.of_eq ringChar_quotient_eq
--  expChar_prime _ p

variable (p f P)

variable [NumberField F] [Algebra F L] [IsCyclotomicExtension {p} ℚ F]

variable {p} in
include hζ in
theorem zeta_sub_one_mem [𝓟.LiesOver 𝒑] : algebraMap (𝓞 F) (𝓞 L) ζ - 1 ∈ 𝓟 := by
  rw [← map_one (f := algebraMap (𝓞 F) (𝓞 L)), ← map_sub, ← mem_comap,
    ← Ideal.under_def, IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p F
      (IsPrimitiveRoot.coe_submonoidClass_iff.mpr hζ) (under (𝓞 F) 𝓟)]
  exact Submodule.mem_span_singleton_self _

variable [NumberField L]

theorem ramificationIdx_eq_p_sub_one [𝓟.LiesOver 𝒑] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    𝓟.ramificationIdx ℤ = p - 1 := by
  simpa using @IsCyclotomicExtension.Rat.ramificationIdx_eq (p * (p ^ f - 1)) (p ^ f - 1) p 0 hp L
    _ _ 𝓟 _ _ _
    (by ring) (not_dvd_pow_self_sub_one p f)

section

variable [NumberField K] [Algebra K L] [IsCyclotomicExtension {p ^ f - 1} ℚ K]

omit [P.HasTeichmullerLift (p ^ f - 1)] in
theorem ramificationIdx_eq_p_sub_one' [𝓟.LiesOver P] [P.LiesOver 𝒑]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    𝓟.ramificationIdx (𝓞 K) = p - 1 := by
  have h𝓟 : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have tower := Ideal.ramificationIdx_tower (R := ℤ) P 𝓟
  rw [@IsCyclotomicExtension.Rat.ramificationIdx_eq (p * (p ^ f - 1)) (p ^ f - 1) p 0 hp L _ _ 𝓟 _
    _ _ (by ring) (not_dvd_pow_self_sub_one p f),
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P (not_dvd_pow_self_sub_one p f),
    one_mul] at tower
  simpa using tower.symm

end

theorem ramificationIdx_under_eq_one [𝓟.LiesOver 𝒑] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    𝓟.ramificationIdx (𝓞 F) = 1 := by
  have h𝓟 : 𝓟 ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using hp.out.ne_zero) 𝓟
  have tower := Ideal.ramificationIdx_tower (R := ℤ) (under (𝓞 F) 𝓟) 𝓟
  rw [@IsCyclotomicExtension.Rat.ramificationIdx_eq (p * (p ^ f - 1)) (p ^ f - 1) p 0 hp L _ _ 𝓟 _
    _ _  (by ring) (not_dvd_pow_self_sub_one p f),
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p F _] at tower
  simp at tower
  have hne : p - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hp.out.one_lt
  nlinarith [Nat.pos_of_ne_zero hne]

end Algebra

section IntermediateField

open IsCyclotomicExtension

variable {L : Type*} [Field L] [NumberField L] (p n : ℕ) [NeZero p] [NeZero n]
  (K F : IntermediateField ℚ L) [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {n} ℚ K]
  [hn : Fact (n.Coprime p)]

include p n in
theorem K_inf_F_eq_bot : K ⊓ F = ⊥ := by
  apply LinearDisjoint.inf_eq_bot
  exact Rat.linearDisjoint_ofCoprime n p K F hn.out

variable [IsCyclotomicExtension {p * n} ℚ L]

include p n in
theorem K_sup_F_eq_top : K ⊔ F = (⊤ : IntermediateField ℚ L) := by
  have : IsCyclotomicExtension {p * n} ℚ (⊤ : IntermediateField ℚ L) :=
    .equiv _ _ _ topEquiv.symm
  have : IsCyclotomicExtension {p * n} ℚ ↑(K ⊔ F) := by
    rw [mul_comm, ← Nat.Coprime.lcm_eq_mul hn.out]
    exact isCyclotomicExtension_lcm_sup ℚ L n p K F
  exact isCyclotomicExtension_eq {p * n}  ℚ L _ _

def galEquiv₀ [Normal ℚ K] [IsGalois F L] : Gal(L/F) ≃* Gal(K/ℚ) :=
  MulEquiv.ofBijective (restrictRestrictAlgEquivMapHom ℚ K F L)
    ⟨restrictRestrictAlgEquivMapHom_injective _ _ (K_sup_F_eq_top p n K F),
    restrictRestrictAlgEquivMapHom_surjective _ _ (K_inf_F_eq_bot p n K F)⟩

def galFEquiv : Gal(L/F) ≃* (ZMod n)ˣ :=
  haveI := isAbelianGalois {p * n} ℚ L
  (galEquiv₀ p n K F).trans <| Rat.galEquivZMod n K

theorem galFEquiv_eq [Normal ℚ K] (σ : Gal(L/F)) :
    galFEquiv p n K F σ = Rat.galEquivZMod n K ((σ.restrictScalars ℚ).restrictNormal K) :=
  rfl

variable {n K F}

theorem IsPrimitiveRoot.galLFEquiv_apply (σ : Gal(L/F)) {η : K} (hη : IsPrimitiveRoot η n) :
    σ (algebraMap K L η) = (algebraMap K L η) ^ (galFEquiv p n K F σ).val.val := by
  have : Normal ℚ K := (isGalois {n} ℚ K).to_normal
  rw [galFEquiv_eq, ← map_pow, ← Rat.galEquivZMod_apply_of_pow_eq _ _ _ hη.pow_eq_one,
    AlgEquiv.restrictNormal_commutes, AlgEquiv.coe_restrictScalars]

theorem IsPrimitiveRoot.galLFEquiv_smul (σ : Gal(L/F)) {η : 𝓞 K} (hη : IsPrimitiveRoot η n) :
    σ • (algebraMap (𝓞 K) (𝓞 L) η) =
      (algebraMap (𝓞 K) (𝓞 L)) η ^ (galFEquiv p n K F σ).val.val := by
  apply RingOfIntegers.coe_injective
  rw [algebraMap.smul', map_pow, ← IsScalarTower.algebraMap_apply, AlgEquiv.smul_def,
    IsScalarTower.algebraMap_apply (𝓞 K) K L]
  exact (hη.map_of_injective <| RingOfIntegers.coe_injective).galLFEquiv_apply p σ

end IntermediateField

--  haveI := IsCyclotomicExtension.isAbelianGalois {p * (p ^ f - 1)} ℚ L
--  (MulEquiv.ofBijective (IntermediateField.restrictRestrictAlgEquivMapHom ℚ K F L)
--    ⟨restrictRestrictAlgEquivMapHom_injective K F (K_sup_F_eq_top p f),
--    restrictRestrictAlgEquivMapHom_surjective K F (K_inf_F_eq_bot p f)⟩)

#exit

omit [P.HasTeichmullerLift (p ^ f - 1)] in
theorem inertia_deg_eq [NeZero f] [P.LiesOver 𝒑] : P.inertiaDeg ℤ = f := by
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := p ^ f - 1) p K P,
    ZMod.orderOf_mod_self_pow_sub_one _ _ hp.out.one_lt]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp (coprime_pow_sub_one p f).symm

include hζ in
omit [IsCyclotomicExtension {p ^ f - 1} ℚ K] [P.IsMaximal] in
theorem zeta_sub_one_not_mem_sq [𝓟.LiesOver 𝒑] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] :
    algebraMap (𝓞 F) (𝓞 L) ζ - 1 ∉ 𝓟 ^ 2 := by
  have hspan : span {ζ - 1} = under (𝓞 F) 𝓟 :=
    (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p F
      (IsPrimitiveRoot.coe_submonoidClass_iff.mpr hζ) (under (𝓞 F) 𝓟)).symm
  have h : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (span {ζ - 1}) ≠ ⊥ := by
    apply map_ne_bot_of_ne_bot
    simpa [sub_eq_zero] using hζ.ne_one hp.out.one_lt
  rw [← map_one (f := algebraMap (𝓞 F) (𝓞 L)), ← map_sub, ← dvd_span_singleton,
    ← Set.image_singleton, ← map_span, FiniteMultiplicity.pow_dvd_iff_le_multiplicity
    (Ideal.finiteMultiplicity IsPrime.ne_top' h), hspan,
    ← IsDedekindDomain.ramificationIdx_eq_multiplicity (under (𝓞 F) 𝓟) 𝓟 (hspan ▸ h),
    ramificationIdx_under_eq_one p f]
  exact Nat.not_succ_le_self 1

variable {p}

variable [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [NeZero f]

variable (p)

include p f in
set_option backward.isDefEq.respectTransparency false in
theorem K_sup_F_eq_top : K ⊔ F = (⊤ : IntermediateField ℚ L) := by
  have : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ (⊤ : IntermediateField ℚ L) :=
      IsCyclotomicExtension.equiv _ _ _ topEquiv.symm
  have : IsCyclotomicExtension {p * (p ^ f - 1)} ℚ ↑(K ⊔ F) := by
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
variable (F K) in
def galEquiv₀ : Gal(L/F) ≃* Gal(K/ℚ) :=
  haveI := IsCyclotomicExtension.isAbelianGalois {p * (p ^ f - 1)} ℚ L
  (MulEquiv.ofBijective (IntermediateField.restrictRestrictAlgEquivMapHom ℚ K F L)
    ⟨restrictRestrictAlgEquivMapHom_injective K F (K_sup_F_eq_top p f),
    restrictRestrictAlgEquivMapHom_surjective K F (K_inf_F_eq_bot p f)⟩)

set_option backward.isDefEq.respectTransparency false in
variable (K) in
def galFEquiv : Gal(L/F) ≃* (ZMod (p ^ f - 1))ˣ :=
  haveI := IsCyclotomicExtension.isAbelianGalois {p * (p ^ f - 1)} ℚ L
  (galEquiv₀ p f F K).trans <| IsCyclotomicExtension.Rat.galEquivZMod (p ^ f - 1) K

include hη in
set_option backward.isDefEq.respectTransparency false in
theorem galLFEquiv_apply_eta (σ : Gal(L/F)) :
    σ • (algebraMap (𝓞 K) (𝓞 L) η) = (algebraMap (𝓞 K) (𝓞 L)) η ^ (galFEquiv p f K σ).val.val := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p ^ f - 1} ℚ K
  have : Normal ℚ K := inferInstance
  convert RingHom.congr_arg (algebraMap (𝓞 K) (𝓞 L))
    <| IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq (p ^ f - 1) K
    (AlgEquiv.restrictNormalHom K (AlgEquiv.restrictScalars ℚ σ)) hη.pow_eq_one
  · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [algebraMap.smul', AlgEquiv.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact (AlgEquiv.restrictNormalHom_apply K (AlgEquiv.restrictScalars ℚ σ) η).symm
  · rw [map_pow]; congr 2

include hη in
set_option backward.isDefEq.respectTransparency false in
theorem galLFEquiv_apply_of_pow_eq_one (σ : Gal(L/F)) {x : 𝓞 L} (hx : x ^ (p ^ f - 1) = 1) :
    σ • x = x ^ (galFEquiv p f K σ).val.val := by
  obtain ⟨a, -, rfl⟩ :=
    (hη.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).eq_pow_of_pow_eq_one hx
  rw [smul_pow', galLFEquiv_apply_eta p f hη, pow_right_comm]

end

end
