module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

set_option linter.style.header false

/-!
# PRed to Mathlib: comparing `restrictHom` with `galRestrict` and `restrictNormalHom`

The declarations in this file were extracted from `SKW.Prereqs.Stickelberger` and submitted
upstream as Mathlib PR [#46233](https://github.com/leanprover-community/mathlib4/pull/46233).
There `IsGaloisGroup.restrictHom_eq_restrictNormal` is replaced by the bundled
`IsGaloisGroup.restrictHom_eq_restrictNormalHom`, and the extra variables of
`IsGaloisGroup.restrictHom_eq_restrictHom` are binders, in the same order.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted, and the usages redirected to the
Mathlib versions.
-/

@[expose] public section

theorem smul_eq_galRestrict_apply (A : Type*) {K L B : Type*} [CommRing A] [Field K] [Field L]
    [CommRing B] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] (σ : Gal(L/K)) (x : B) :
    σ • x = galRestrict A K L B σ x := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [algebraMap.smul', AlgEquiv.smul_def, algebraMap_galRestrict_apply]

/-- `restrictHom` is `AlgEquiv.restrictNormal`. -/
theorem IsGaloisGroup.restrictHom_eq_restrictNormal (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional K L]
    [FiniteDimensional K E] [IsGalois K L] [IsGalois K E] (σ : Gal(L/K)) :
    IsGaloisGroup.restrictHom Gal(L/K) Gal(E/K) K E L σ = σ.restrictNormal E := by
  ext x
  apply (algebraMap E L).injective
  rw [← AlgEquiv.smul_def, IsGaloisGroup.algebraMap_restrictHom_smul, AlgEquiv.smul_def,
    AlgEquiv.restrictNormal_commutes]

section restrictHom_eq

variable (G G' A B C A' B' C' : Type*) [Group G] [Group G'] [Finite G] [Finite G']
  [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower A B C] [FaithfulSMul B C]
  [MulSemiringAction G C] [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B]
  [CommRing A'] [CommRing B'] [CommRing C'] [IsDomain C'] [Algebra A' B'] [Algebra A' C']
  [Algebra B' C'] [IsScalarTower A' B' C'] [FaithfulSMul B' C']
  [MulSemiringAction G C'] [IsGaloisGroup G A' C'] [MulSemiringAction G' B']
  [IsGaloisGroup G' A' B']
  [Algebra B B'] [Algebra C C'] [Algebra B C'] [IsScalarTower B B' C'] [IsScalarTower B C C']
  [FaithfulSMul B B'] [SMulDistribClass G C C'] [SMulDistribClass G' B B']

/-- `restrictHom` does not depend on the tower `C/B/A` used to define it, as long as the
actions of `G` and `G'` are compatible with the maps `B → B'` and `C → C'`. -/
theorem IsGaloisGroup.restrictHom_eq_restrictHom :
    IsGaloisGroup.restrictHom G G' A B C = IsGaloisGroup.restrictHom G G' A' B' C' := by
  ext g
  have : FaithfulSMul G' B := IsGaloisGroup.faithful A
  refine eq_of_smul_eq_smul (α := B) fun x ↦ ?_
  apply FaithfulSMul.algebraMap_injective B B'
  apply FaithfulSMul.algebraMap_injective B' C'
  rw [← IsScalarTower.algebraMap_apply B B' C', IsScalarTower.algebraMap_apply B C C',
    IsGaloisGroup.algebraMap_restrictHom_smul, algebraMap.smul',
    ← IsScalarTower.algebraMap_apply B C C', algebraMap.smul',
    IsGaloisGroup.algebraMap_restrictHom_smul, ← IsScalarTower.algebraMap_apply B B' C']

end restrictHom_eq
