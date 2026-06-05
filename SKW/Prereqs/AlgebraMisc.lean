module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.FieldTheory.LinearDisjoint

public import Mathlib.Algebra.Algebra.Hom.Rat

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

variable {R S : Type*}

/-- Reinterpret a `RingEquiv as a `ℚ`-algebra isomorphism. This actually yields an equivalence,
see `RingEquiv.equivRatAlgEquiv`. -/
def RingEquiv.toRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) : R ≃ₐ[ℚ] S :=
  { f with commutes' := f.toRingHom.map_rat_algebraMap }

@[simp]
theorem RingEquiv.toRatAlgEquiv_toRingEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) :
    ↑f.toRatAlgEquiv = f :=
  RingEquiv.ext fun _ ↦ rfl

@[simp]
theorem RingEquiv.toRatAlgEquiv_apply [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) (x : R) :
    f.toRatAlgEquiv x = f x :=
  rfl

@[simp]
theorem AlgEquiv.toRingEquiv_toRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R ≃ₐ[ℚ] S) : (f : R ≃+* S).toRatAlgEquiv = f :=
  AlgEquiv.ext fun _ => rfl

/-- The equivalence between `RingEquiv` and `ℚ`-algebra isomorphisms. -/
def RingEquiv.equivRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] :
    (R ≃+* S) ≃ (R ≃ₐ[ℚ] S) where
  toFun := RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv
  left_inv f := RingEquiv.toRatAlgEquiv_toRingEquiv f
  right_inv f := AlgEquiv.toRingEquiv_toRatAlgEquiv f

/-- Reinterpret a `RingEquiv` as a `ℤ`-algebra isomorphism. -/
def RingEquiv.toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : R ≃ₐ[ℤ] S :=
  { f with commutes' := fun n ↦ by simp }

@[simp]
lemma RingEquiv.toIntAlgEquiv_coe [Ring R] [Ring S] (f : R ≃+* S) :
    ⇑f.toIntAlgEquiv = ⇑f := rfl

lemma RingEquiv.toIntAlgEquiv_apply [Ring R] [Ring S] (f : R ≃+* S) (x : R) :
    f.toIntAlgEquiv x = f x := rfl

lemma RingEquiv.toIntAlgEquiv_injective [Ring R] [Ring S] :
    Function.Injective (RingEquiv.toIntAlgEquiv : (R ≃+* S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

end
