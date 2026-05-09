module

public import SKW.Stickelberger.GaussSum

@[expose] public section

noncomputable section

open Ideal NumberField IntermediateField Pointwise

variable (p f : ℕ) [NeZero (p ^ f - 1)]

local notation3 "𝒑" => span {(p : ℤ)}

variable {p f}

variable {L : Type*} [Field L] [NumberField L] {F K : IntermediateField ℚ L} {P : Ideal (𝓞 K)}

variable (hbij : Function.Bijective (rootsOfUnity.mapQuot (p ^ f - 1) P))

variable {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p) {η : 𝓞 K} (hη : IsPrimitiveRoot η (p ^ f - 1))

variable [P.IsMaximal] (𝓟 : Ideal (𝓞 L)) [hp : Fact (p.Prime)]
  [𝓟.IsPrime]

local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

def valGauss [P.LiesOver 𝒑] (a : ℤ) : ℕ := multiplicity 𝓟 (span {(GaussSum hbij hζ a : 𝓞 L)})

include hη in
theorem valGauss_eq_zero [P.LiesOver 𝒑] (a : ℤ) (h : ↑(p ^ f - 1 : ℕ) ∣ a) :
    valGauss hbij hζ 𝓟 a = 0 := by
  rw [valGauss, GaussSum, orderOf_dvd_iff_zpow_eq_one.mp, MulChar.ringHomComp_one,
    gaussSum_one_left, span_singleton_neg, span_singleton_one, multiplicity_bot]
  · exact IsPrime.ne_top'
  · rw [ne_eq, MonoidHom.compAddChar_eq_one_iff (FaithfulSMul.algebraMap_injective _ _)]
    exact addCharTrace_ne_one P hζ
  · rwa [orderOf_teichmuller hbij hη, Int.dvd_neg]

variable [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
[IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]

theorem multiplicity_smul_GaussSum [P.LiesOver 𝒑] [Fact (Odd p)] (σ : Gal(L/F)) :
    multiplicity (σ • 𝓟) (span {(GaussSum hbij hζ 1 : 𝓞 L)}) =
      valGauss hbij hζ 𝓟 (galFEquiv p f K σ⁻¹).val.val := by
  rw [← multiplicity_map_eq (Ideal.mapEquiv (MulSemiringAction.toRingEquiv Gal(L/F) (𝓞 L) σ⁻¹))
    (a := σ • 𝓟), mapEquiv_apply, mapEquiv_apply]
  erw [← pointwise_smul_def]
  rw [inv_smul_smul, valGauss, ← gal_gaussSum_eq_gaussSum hbij hζ hη σ⁻¹, map_span,
    Set.image_singleton, MulSemiringAction.toRingEquiv_apply]

variable [Fact (Odd p)]
