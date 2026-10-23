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

variable [NumberField L]

end Algebra

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
