module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

public import SKW.PRed2Mathlib.AlgebraMisc

@[expose] public section

theorem Algebra.adjoin_singleton_add {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A)
    (y : R) : adjoin R {x + algebraMap R A y} = adjoin R {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact add_mem (self_mem_adjoin_singleton R x) (algebraMap_mem _ y)
  · apply adjoin_singleton_le
    convert Subalgebra.sub_mem _ (self_mem_adjoin_singleton R _) (algebraMap_mem _ y)
    rw [add_sub_cancel_right]

theorem IntermediateField.adjoin_simple_add {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (y : F) : adjoin F {x + algebraMap F E y} = adjoin F {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact add_mem (mem_adjoin_simple_self F x) (algebraMap_mem _ y)
  · rw [adjoin_simple_le_iff]
    convert IntermediateField.sub_mem _ (mem_adjoin_simple_self F _) (algebraMap_mem _ y)
    rw [eq_sub_iff_add_eq]

theorem IntermediateField.adjoin_simple_mul {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (y : F) (hy : y ≠ 0) : adjoin F {x * algebraMap F E y} = adjoin F {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact mul_mem (mem_adjoin_simple_self F x) (algebraMap_mem _ y)
  · rw [adjoin_simple_le_iff]
    convert IntermediateField.div_mem _ (mem_adjoin_simple_self F _) (algebraMap_mem _ y)
    rw [mul_div_cancel_right₀ x (by rwa [map_ne_zero])]

@[simp]
theorem Subgroup.map_top {G : Type*} [Group G] {N : Type*} [Group N] (f : G →* N) :
    map f ⊤ = f.range := (MonoidHom.range_eq_map f).symm

/-! ### MulEquiv / AlgHom / AlgEquiv -/

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

end
