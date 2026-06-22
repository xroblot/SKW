module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.Normal.Basic

/-!
# PRed to Mathlib: the compositum of two abelian extensions is abelian

The declarations in this file were extracted from `SKW.Prereqs.Normal` and submitted upstream as
Mathlib PR [#40905](https://github.com/leanprover-community/mathlib4/pull/40905).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
(and its import in `SKW.Prereqs.Normal`) should be deleted, and any usages redirected to the
Mathlib versions.
-/

@[expose] public section

variable {F : Type*} [Field F]

/-- The kernel of the restriction homomorphism `Gal(K₁/F) →* Gal(E/F)` is the subgroup fixing
the image of `E` in `K₁` pointwise. -/
theorem AlgEquiv.ker_restrictNormalHom {K₁ : Type*} [Field K₁] [Algebra F K₁]
    (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [IsScalarTower F E K₁] [Normal F E] :
    (AlgEquiv.restrictNormalHom E (K₁ := K₁)).ker
      = (IsScalarTower.toAlgHom F E K₁).fieldRange.fixingSubgroup := by
  ext σ
  simp only [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff, AlgEquiv.ext_iff,
    AlgHom.mem_fieldRange, IsScalarTower.coe_toAlgHom', AlgEquiv.one_apply]
  refine ⟨?_, fun h y ↦
    (algebraMap E K₁).injective ((AlgEquiv.restrictNormal_commutes σ E y).trans (h _ ⟨y, rfl⟩))⟩
  rintro h x ⟨y, rfl⟩
  exact (AlgEquiv.restrictNormal_commutes σ E y).symm.trans (congrArg (algebraMap E K₁) (h y))

namespace IntermediateField

variable {E : Type*} [Field E] [Algebra F E]

/-- The restriction homomorphism embedding the automorphism group of a compositum `K ⊔ L`
into the product of the automorphism groups of two normal factors `K` and `L`,
`σ ↦ (σ|_K, σ|_L)`. -/
@[simps apply]
noncomputable def restrictNormalHomSupProd (K L : IntermediateField F E) [Normal F K] [Normal F L] :
    Gal(↑(K ⊔ L)/F) →* Gal(K/F) × Gal(L/F) :=
  letI : Algebra K ↑(K ⊔ L) := (inclusion le_sup_left).toAlgebra
  letI : Algebra L ↑(K ⊔ L) := (inclusion le_sup_right).toAlgebra
  { toFun σ := (AlgEquiv.restrictNormalHom K σ, AlgEquiv.restrictNormalHom L σ)
    map_one' := by simp
    map_mul' := by simp }

/-- The restriction homomorphism into the product of the two factor automorphism groups is
injective: an automorphism of the compositum is determined by its restrictions to `K` and `L`. -/
theorem restrictNormalHomSupProd_injective (K L : IntermediateField F E) [Normal F K] [Normal F L] :
    Function.Injective (restrictNormalHomSupProd K L) := by
  letI : Algebra K ↑(K ⊔ L) := (inclusion le_sup_left).toAlgebra
  letI : Algebra L ↑(K ⊔ L) := (inclusion le_sup_right).toAlgebra
  rw [← MonoidHom.ker_eq_bot_iff]
  suffices (IsScalarTower.toAlgHom F K ↑(K ⊔ L)).fieldRange ⊔
      (IsScalarTower.toAlgHom F L ↑(K ⊔ L)).fieldRange = ⊤ by
    rw [← fixingSubgroup_top, ← this, fixingSubgroup_sup, ← AlgEquiv.ker_restrictNormalHom,
      ← AlgEquiv.ker_restrictNormalHom]
    exact MonoidHom.ker_prod _ _
  change restrict (le_sup_left : K ≤ K ⊔ L) ⊔ restrict (le_sup_right : L ≤ K ⊔ L) = ⊤
  exact lift_injective _ <| by simp [lift_sup, lift_restrict, lift_top]

end IntermediateField

/-- The compositum of two abelian extensions is abelian: its Galois group embeds into the product
of the (commutative) factor Galois groups. -/
instance IsAbelianGalois.sup {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) [IsAbelianGalois F K] [IsAbelianGalois F L] :
    IsAbelianGalois F ↑(K ⊔ L) :=
  haveI : IsMulCommutative Gal(↑(K ⊔ L)/F) :=
    .of_comm fun a b ↦ IntermediateField.restrictNormalHomSupProd_injective K L <| by
      rw [map_mul, map_mul, mul_comm']
  { }

end
