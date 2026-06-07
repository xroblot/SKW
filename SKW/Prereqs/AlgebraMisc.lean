module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.FieldTheory.LinearDisjoint

public import Mathlib.Algebra.Algebra.Hom.Rat

public import SKW.PRed2Mathlib.AlgebraMisc

@[expose] public section

/-! ### MulEquiv / AlgHom / AlgEquiv -/

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

end
