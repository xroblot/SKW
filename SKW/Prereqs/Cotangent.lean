module

public import SKW.Prereqs.LinearAlgebra
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import SKW.Prereqs.Ideals

/-!
# The cotangent line of a maximal ideal

For a maximal ideal `I` of a commutative ring `R`, the cotangent space `I ⧸ I ^ 2` is intrinsic to
the local ring `R_I = Localization.AtPrime I`: it is semilinearly isomorphic
(`Ideal.cotangentEquivCotangentSpace`, over the residue-field identification `R ⧸ I ≃ κ(I)`) to the
cotangent space of `R_I`. When `R` is a Dedekind domain and `I ≠ ⊥`, `R_I` is a discrete valuation
ring, so this cotangent space is a line over the residue field (`Ideal.finrank_cotangent_eq_one`).

These are intended for eventual upstreaming to Mathlib.
-/

@[expose] public section

open Module

/-- For a maximal ideal `I`, `R ⧸ I` is already its own fraction field, so the canonical map to
the residue field `κ(I) = ResidueField R_I` of the localization is an isomorphism. -/
noncomputable def Ideal.residueFieldEquiv {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    R ⧸ I ≃+* I.ResidueField :=
  RingEquiv.ofBijective _ I.bijective_algebraMap_quotient_residueField

open IsLocalization.AtPrime IsLocalRing

/-! ### The cotangent line of a maximal ideal, via the natural map `Ideal.mapₗ` -/

/-- The natural map `I ⧸ I ^ 2 → (I.map f) ⧸ (I.map f) ^ 2` induced by `f = algebraMap R Rₚ`,
built as `Submodule.mapQ` of `Ideal.mapₗ`. Although `mapₗ` is `f`-semilinear, the map is honestly
`R`-linear (the `R`-action on the target factors through `f`), and it has the defining (`rfl`)
apply lemma `cotangentMap (toCotangent x) = toCotangent (mapₗ f x)`. -/
noncomputable def Ideal.cotangentMap {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    I.Cotangent →ₗ[R] (I.map (algebraMap R (Localization.AtPrime I))).Cotangent :=
  let g := Submodule.mapQ (I • ⊤) ((I.map (algebraMap R (Localization.AtPrime I))) • ⊤)
    (I.mapₗ (algebraMap R (Localization.AtPrime I))) (by
      intro x hx
      refine Submodule.smul_induction_on hx (fun a ha b _ ↦ ?_) (fun _ _ ↦ add_mem)
      rw [Submodule.mem_comap, map_smulₛₗ]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top)
  { toAddHom := g.toAddHom
    map_smul' := fun r c => (map_smulₛₗ g r c).trans (algebraMap_smul _ r (g c)) }

@[simp]
theorem Ideal.cotangentMap_toCotangent {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal]
    (x : I) :
    I.cotangentMap (I.toCotangent x)
      = (I.map (algebraMap R (Localization.AtPrime I))).toCotangent
        (I.mapₗ (algebraMap R (Localization.AtPrime I)) x) := rfl

/-- **Injectivity** (kernel `I ^ 2`): `cotangentMap (toCotangent x) = 0 ↔ algebraMap x ∈ 𝔪 ^ 2 ↔
x ∈ I ^ 2` (`under_maximalIdeal_pow`). -/
theorem Ideal.cotangentMap_injective {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Function.Injective I.cotangentMap := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective a
  rw [Ideal.cotangentMap_toCotangent, Ideal.toCotangent_eq_zero, Ideal.coe_mapₗ_apply,
    Localization.AtPrime.map_eq_maximalIdeal] at ha
  -- `ha : algebraMap x ∈ 𝔪 ^ 2`; goal `(x : R) ∈ I ^ 2 = (𝔪 ^ 2).under R`.
  rw [Ideal.toCotangent_eq_zero,
    ← IsLocalization.AtPrime.under_maximalIdeal_pow I (Localization.AtPrime I) 2, Ideal.mem_under]
  exact ha

/-- **Surjectivity**: a class in `𝔪 ⧸ 𝔪 ^ 2` is `toCotangent ⟨y, _⟩` with `y ∈ 𝔪`; pulling the
class of `y` back along `R ⧸ I ^ 2 ≃ Rₚ ⧸ 𝔪 ^ 2` (`equivQuotMaximalIdealPow`) gives `a ∈ R` with
`algebraMap a ≡ y` mod `𝔪 ^ 2` (so the same cotangent class) and `algebraMap a ∈ 𝔪` (so `a ∈ I`). -/
theorem Ideal.cotangentMap_surjective {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Function.Surjective I.cotangentMap := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ :=
    (I.map (algebraMap R (Localization.AtPrime I))).toCotangent_surjective z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((IsLocalization.AtPrime.equivQuotMaximalIdealPow I (Localization.AtPrime I) 2).symm
      (Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime I) ^ 2) y))
  have hkey : Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime I) ^ 2)
        (algebraMap R (Localization.AtPrime I) a)
      = Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime I) ^ 2) y := by
    rw [← IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk I (Localization.AtPrime I) 2 a,
      ha, AlgEquiv.apply_symm_apply]
  have hsub : algebraMap R (Localization.AtPrime I) a - y
      ∈ maximalIdeal (Localization.AtPrime I) ^ 2 :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hkey
  have hsub' : algebraMap R (Localization.AtPrime I) a - y
      ∈ (I.map (algebraMap R (Localization.AtPrime I))) ^ 2 := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]; exact hsub
  have haI : a ∈ I := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime I) I a,
      show algebraMap R (Localization.AtPrime I) a
        = (algebraMap R (Localization.AtPrime I) a - y) + y from by ring]
    exact add_mem (Ideal.pow_le_self two_ne_zero hsub)
      (by rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact hy)
  refine ⟨I.toCotangent ⟨a, haI⟩, ?_⟩
  rw [Ideal.cotangentMap_toCotangent, Ideal.toCotangent_eq, Ideal.coe_mapₗ_apply]
  exact hsub'

/-- Cotangent functoriality along an equality of ideals: `h : I = J` induces `I.Cotangent ≃ₗ
J.Cotangent`. (Used to bridge `(I.map (algebraMap R Rₚ)).Cotangent` and `CotangentSpace Rₚ`.) -/
def Ideal.cotangentEquivOfEq {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent :=
  Submodule.Quotient.equiv (I • ⊤) (J • ⊤) (LinearEquiv.ofEq I J h) (by subst h; simp)

/-- The cotangent line `I ⧸ I ^ 2` is intrinsic to the local ring at `I`: it is additively
isomorphic to the cotangent space of `Rₚ = Localization.AtPrime I`. It is `AddEquiv.ofBijective` of
the natural map `cotangentMap`, post-composed with the bridge `(I.map (algebraMap R Rₚ)).Cotangent ≃
CotangentSpace Rₚ` coming from `I.map (algebraMap R Rₚ) = 𝔪` (`map_eq_maximalIdeal`). -/
noncomputable def Ideal.cotangentEquivCotangentSpace {R : Type*} [CommRing R] (I : Ideal R)
    [I.IsMaximal] :
    I.Cotangent ≃+ IsLocalRing.CotangentSpace (Localization.AtPrime I) :=
  (AddEquiv.ofBijective I.cotangentMap.toAddMonoidHom
      ⟨I.cotangentMap_injective, I.cotangentMap_surjective⟩).trans
    (Ideal.cotangentEquivOfEq Localization.AtPrime.map_eq_maximalIdeal).toAddEquiv

@[simp]
theorem Ideal.cotangentEquivCotangentSpace_apply {R : Type*} [CommRing R] (I : Ideal R)
    [I.IsMaximal] (z : I.Cotangent) :
    I.cotangentEquivCotangentSpace z
      = Ideal.cotangentEquivOfEq Localization.AtPrime.map_eq_maximalIdeal (I.cotangentMap z) := rfl

/-- `Ideal.cotangentEquivCotangentSpace` is semilinear over the residue-field identification
`Ideal.residueFieldEquiv : R ⧸ I ≃+* κ(I)`: the underlying maps `cotangentMap` and
`cotangentEquivOfEq` are `R`-linear, and `R` acts on `CotangentSpace Rₚ` through `κ(I)`. -/
theorem Ideal.cotangentEquivCotangentSpace_smul {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal]
    (c : R ⧸ I) (x : I.Cotangent) :
    I.cotangentEquivCotangentSpace (c • x)
      = I.residueFieldEquiv c • I.cotangentEquivCotangentSpace x := by
  -- `cotangentEquivCotangentSpace` is `R`-linear, pulling out scalars as `algebraMap R Rₚ`:
  have hlin : ∀ (s : R) (z : I.Cotangent), I.cotangentEquivCotangentSpace (s • z)
      = algebraMap R (Localization.AtPrime I) s • I.cotangentEquivCotangentSpace z := fun s z => by
    simp only [Ideal.cotangentEquivCotangentSpace_apply]
    rw [map_smul, ← algebraMap_smul (Localization.AtPrime I) s (I.cotangentMap z), map_smul]
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [show (Ideal.Quotient.mk I r) • x = r • x from by
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul], hlin,
    show I.residueFieldEquiv (Ideal.Quotient.mk I r) = algebraMap R I.ResidueField r from rfl,
    IsScalarTower.algebraMap_apply R (Localization.AtPrime I) I.ResidueField,
    algebraMap_smul I.ResidueField (algebraMap R (Localization.AtPrime I) r)]

/-- For a maximal ideal `I ≠ ⊥` of a Dedekind domain, the cotangent space `I ⧸ I ^ 2` is a
one-dimensional vector space over the residue field `R ⧸ I`. (Locally at `I` the ring is a
discrete valuation ring, and this is its cotangent line.) -/
theorem Ideal.finrank_cotangent_eq_one {R : Type*} [CommRing R] [IsDedekindDomain R] (I : Ideal R)
    [I.IsMaximal] (hI : I ≠ ⊥) : finrank (R ⧸ I) I.Cotangent = 1 := by
  have : IsDiscreteValuationRing (Localization.AtPrime I) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hI (Localization.AtPrime I)
  rw [finrank_eq_of_equiv_equiv I.residueFieldEquiv I.cotangentEquivCotangentSpace
    I.residueFieldEquiv.bijective I.cotangentEquivCotangentSpace_smul]
  exact IsLocalRing.finrank_CotangentSpace_eq_one (Localization.AtPrime I)
