module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

theorem Ideal.absNorm_eq_card {S : Type*} [CommRing S] [Nontrivial S] [IsDedekindDomain S]
    [Module.Free ℤ S] (I : Ideal S) :
    Ideal.absNorm I = Nat.card (S ⧸ I) := rfl
