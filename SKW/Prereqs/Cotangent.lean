module

public import SKW.Prereqs.LinearAlgebra
public import Mathlib.RingTheory.Ideal.Cotangent
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

open IsLocalization.AtPrime IsLocalRing

/-! ### The cotangent line of a maximal ideal -/

variable {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal]

local notation3 "R_I" => Localization.AtPrime I

/-- The natural map `I ⧸ I ^ 2 → 𝔪 ⧸ 𝔪 ^ 2` induced by `algebraMap R R_I`, landing directly in
`CotangentSpace R_I`, built as `Submodule.mapQ` of `algebraMap R R_I` corestricted to
`maximalIdeal R_I` (`to_map_mem_maximal_iff`). It is `R`-linear (the `R`-action on the target
factors through `algebraMap`), with apply lemma
`cotangentMap (toCotangent x) = toCotangent ⟨algebraMap x, _⟩`. -/
noncomputable def Ideal.cotangentMap : I.Cotangent →ₗ[R] CotangentSpace R_I :=
  let g := Submodule.mapQ (I • ⊤) (maximalIdeal R_I • ⊤)
    ((algebraMap R R_I).toSemilinearMap.restrict
      (fun x hx ↦ (to_map_mem_maximal_iff R_I I x).mpr hx)) (fun x hx ↦ by
        refine Submodule.smul_induction_on hx (fun a ha _ _ ↦ ?_) (fun _ _ ↦ add_mem)
        rw [Submodule.mem_comap, map_smulₛₗ]
        exact Submodule.smul_mem_smul ((to_map_mem_maximal_iff R_I I a).mpr ha) Submodule.mem_top)
  { toAddHom := g.toAddHom
    map_smul' := fun r c ↦ (map_smulₛₗ g r c).trans (algebraMap_smul _ r (g c)) }

theorem cotangentMap_mk_smul (r : R) (x : I.Cotangent) :
    I.cotangentMap (Ideal.Quotient.mk I r • x) = r • I.cotangentMap x :=
  LinearMap.map_smul I.cotangentMap r x

@[simp]
theorem Ideal.cotangentMap_toCotangent (x : I) :
    I.cotangentMap (I.toCotangent x)
      = (maximalIdeal R_I).toCotangent
        ⟨algebraMap R R_I x, (to_map_mem_maximal_iff R_I I x).mpr x.2⟩ := rfl

/-- **Injectivity** (kernel `I ^ 2`): `cotangentMap (toCotangent x) = 0 ↔ algebraMap x ∈ 𝔪 ^ 2 ↔
x ∈ I ^ 2` (`under_maximalIdeal_pow`). -/
theorem Ideal.cotangentMap_injective : Function.Injective I.cotangentMap := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective a
  rw [cotangentMap_toCotangent, toCotangent_eq_zero] at ha
  rwa [toCotangent_eq_zero, ← under_maximalIdeal_pow I R_I 2, mem_under]

/-- **Surjectivity**: a class in `𝔪 ⧸ 𝔪 ^ 2` is `toCotangent ⟨y, _⟩` with `y ∈ 𝔪`; pulling the
class of `y` back along `R ⧸ I ^ 2 ≃ Rₚ ⧸ 𝔪 ^ 2` (`equivQuotMaximalIdealPow`) gives `a ∈ R` with
`algebraMap a ≡ y` mod `𝔪 ^ 2` (so the same cotangent class) and `algebraMap a ∈ 𝔪` (so `a ∈ I`). -/
theorem Ideal.cotangentMap_surjective :
    Function.Surjective I.cotangentMap := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := (maximalIdeal R_I).toCotangent_surjective z
  obtain ⟨a, ha⟩ := Quotient.mk_surjective ((equivQuotMaximalIdealPow I R_I 2).symm y)
  replace ha : Quotient.mk (maximalIdeal R_I ^ 2) (algebraMap R R_I a)
      = Quotient.mk (maximalIdeal R_I ^ 2) y := by
    rw [← equivQuotMaximalIdealPow_apply_mk I R_I 2 a, ha, AlgEquiv.apply_symm_apply]
  refine ⟨I.toCotangent ⟨a, ?_⟩, ?_⟩
  · rw [← to_map_mem_maximal_iff R_I I, ← mk_mem_cotangentIdeal, ha]
    exact mk_mem_cotangentIdeal.mpr hy
  · simpa [cotangentMap_toCotangent, toCotangent_eq, ← Quotient.mk_eq_mk_iff_sub_mem]

/-- The cotangent line `I ⧸ I ^ 2` is intrinsic to the local ring at `I`: it is additively
isomorphic to the cotangent space of `R_I`, as `AddEquiv.ofBijective` of `cotangentMap`. -/
noncomputable def Ideal.cotangentEquivCotangentSpace : I.Cotangent ≃+ CotangentSpace R_I :=
  AddEquiv.ofBijective I.cotangentMap.toAddMonoidHom
    ⟨I.cotangentMap_injective, I.cotangentMap_surjective⟩

@[simp]
theorem Ideal.cotangentEquivCotangentSpace_apply (z : I.Cotangent) :
    I.cotangentEquivCotangentSpace z = I.cotangentMap z := rfl

/-- `Ideal.cotangentEquivCotangentSpace` is semilinear over the residue-field identification
`Ideal.residueFieldEquiv : R ⧸ I ≃+* κ(I)`: `cotangentMap` is `R`-linear, and `R` acts on
`CotangentSpace R_I` through `κ(I)`. -/
theorem Ideal.cotangentEquivCotangentSpace_smul (c : R ⧸ I) (x : I.Cotangent) :
    I.cotangentEquivCotangentSpace (c • x)
      = I.residueFieldEquiv c • I.cotangentEquivCotangentSpace x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [cotangentEquivCotangentSpace_apply, cotangentMap_mk_smul, residueFieldEquiv_mk,
    IsScalarTower.algebraMap_apply R R_I I.ResidueField, algebraMap_smul]

/-- If the localization `R_I` of `R` at a maximal ideal `I` is a discrete valuation ring, then the
cotangent space `I ⧸ I ^ 2` is a one-dimensional vector space over the residue field `R ⧸ I` (its
cotangent line). This is a local statement: only the local ring at `I` matters. -/
theorem Ideal.finrank_cotangent_eq_one [IsDomain R] [IsDiscreteValuationRing R_I] :
    finrank (R ⧸ I) I.Cotangent = 1 := by
  rw [finrank_eq_of_equiv_equiv I.residueFieldEquiv I.cotangentEquivCotangentSpace
    I.residueFieldEquiv.bijective I.cotangentEquivCotangentSpace_smul]
  exact IsLocalRing.finrank_CotangentSpace_eq_one R_I

/-! ### The action of the stabilizer on the cotangent space

A group `M` acting on `R` by ring automorphisms acts additively on the cotangent space
`I.Cotangent` through its stabilizer subgroup `MulAction.stabilizer M I`: an element `g` preserving
`I` sends `I.toCotangent x ↦ I.toCotangent ⟨g • x, _⟩` (`DistribMulAction`). The same stabilizer acts
on the residue ring `R ⧸ I` (`MulSemiringAction`), and the cotangent action is *semilinear* over it:
`g • (c • v) = (g • c) • (g • v)` (`stabilizer_smul_smul`). Conjugation identities are then free via
`mul_smul`.

Names provisional, pending `lean:mathlib-review`.
-/

section Action

namespace Ideal

open scoped Pointwise

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [Group M] [MulSemiringAction M R]


/-- The stabilizer of `I` acts on the cotangent space `I.Cotangent` -/
instance : SMul (MulAction.stabilizer M I) I.Cotangent where
  smul m v :=
    Submodule.mapQ (I • ⊤) (I • ⊤)
      ((MulSemiringAction.toRingHom M R (m : M)).toSemilinearMap.restrict
        (fun x hx ↦ Ideal.smul_mem_of_mem_stabilizer I m hx))
        (fun x hx ↦ by
          rw [Submodule.mem_smul_top_iff, smul_eq_mul, ← pow_two] at hx
          simp only [Submodule.mem_comap, LinearMap.restrict_apply, Submodule.mem_smul_top_iff,
            smul_eq_mul, ← pow_two]
          exact Ideal.smul_mem_pow_of_mem_stabilizer I m hx) v

theorem smul_toCotangent (m : MulAction.stabilizer M I) (x : I) :
    m • I.toCotangent x = I.toCotangent ⟨m • x, I.smul_mem_of_mem_stabilizer m x.prop⟩ := rfl

/-- The stabilizer of `I` acts additively on the cotangent space `I.Cotangent` -/
instance : DistribMulAction (MulAction.stabilizer M I) I.Cotangent where
  mul_smul m n v := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    simp [smul_toCotangent, smul_smul]
  one_smul v := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    simp [smul_toCotangent]
  smul_zero m := by
    rw [← LinearMap.map_zero I.toCotangent, smul_toCotangent, toCotangent_eq]
    simp
  smul_add m v w := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective w
    simp [← map_add, smul_toCotangent]

/-- The stabilizer of `I` acts on the residue ring `R ⧸ I`. -/
instance : SMul (MulAction.stabilizer M I) (R ⧸ I) where
  smul m x := Ideal.quotientMap I (MulSemiringAction.toRingHom M R (m : M))
    (fun _ hy ↦ Ideal.smul_mem_of_mem_stabilizer I m hy) x

theorem stabilizer_smul_mk (m : MulAction.stabilizer M I) (x : R) :
    m • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (m • x) := rfl

/-- The stabilizer of `I` acts on the residue ring `R ⧸ I` by ring automorphisms. -/
instance : MulSemiringAction (MulAction.stabilizer M I) (R ⧸ I) where
  one_smul q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [stabilizer_smul_mk]
  mul_smul m n q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [stabilizer_smul_mk, mul_smul]
  smul_zero m := by
    rw [← map_zero (Ideal.Quotient.mk I), stabilizer_smul_mk, smul_zero]
  smul_add m q r := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [stabilizer_smul_mk, ← map_add, smul_add]
  smul_one m := by rw [← map_one (Ideal.Quotient.mk I), stabilizer_smul_mk, smul_one]
  smul_mul m q r := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [stabilizer_smul_mk, ← map_mul]

/-- The stabilizer action on `R ⧸ I` is compatible with the `R`-algebra structure:
`g • (r • c) = (g • r) • (g • c)`. -/
instance : SMulDistribClass (MulAction.stabilizer M I) R (R ⧸ I) where
  smul_distrib_smul g r s := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective s
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, stabilizer_smul_mk, ← map_mul]

/-- The cotangent action is semilinear over the residue action. -/
theorem stabilizer_smul_smul (g : MulAction.stabilizer M I) (c : R ⧸ I) (v : I.Cotangent) :
    g • (c • v) = (g • c) • (g • v) := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [stabilizer_smul_mk, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, ← map_smul,
    smul_toCotangent, smul_toCotangent, algebraMap_smul, ← map_smul, toCotangent_eq]
  simp

/-- An inertia element acts trivially on the residue ring `R ⧸ I`. -/
theorem inertia_smul_residue (τ : I.inertia (MulAction.stabilizer M I)) (c : R ⧸ I) :
    (τ : MulAction.stabilizer M I) • c = c := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [stabilizer_smul_mk, Ideal.Quotient.eq]
  exact τ.prop x

/-- The inertia action on the cotangent space is `R ⧸ I`-linear: it commutes with the residue
scalar action. This makes `DistribMulAction.toModuleAut (R ⧸ I) I.Cotangent` an `R ⧸ I`-linear
action of the inertia group (a replacement for `cotangentInertiaAction`). -/
instance : SMulCommClass (I.inertia (MulAction.stabilizer M I)) (R ⧸ I) I.Cotangent where
  smul_comm τ c v := by
    rw [MulAction.subgroup_smul_def, stabilizer_smul_smul, inertia_smul_residue,
      ← MulAction.subgroup_smul_def]

end Ideal

end Action
