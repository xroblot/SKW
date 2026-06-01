module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.FieldTheory.LinearDisjoint

@[expose] public section

/-! ### MulEquiv / AlgHom / AlgEquiv -/

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

noncomputable def AlgHom.equivFieldRange {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] (f : L →ₐ[K] L') :
    L ≃ₐ[K] f.fieldRange :=
  (AlgEquiv.ofBijective
    (f.codRestrict f.range fun x ↦ AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    ⟨fun _ _ h ↦ f.injective (congr_arg Subtype.val h),
     fun ⟨_, hy⟩ ↦ (AlgHom.mem_fieldRange.mp hy).imp fun _ hx => Subtype.ext hx⟩)

@[simp]
theorem equivFieldRange_apply {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] (f : L →ₐ[K] L') (x : L) : f.equivFieldRange x = f x :=
  rfl
