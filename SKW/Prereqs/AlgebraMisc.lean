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

/-! ### MulEquiv / AlgHom / AlgEquiv -/

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

/-! ### Coprime exponent power extraction -/

/-- If `x ^ m = y ^ n` with `m` and `n` coprime and `x ≠ 0`, then `x` is itself an `n`-th power. -/
theorem exists_eq_pow_of_pow_eq_pow_of_coprime {G : Type*} [CommGroupWithZero G] {m n : ℕ}
    (hmn : Nat.Coprime m n) {x y : G} (hx : x ≠ 0) (h : x ^ m = y ^ n) :
    ∃ z : G, z ≠ 0 ∧ x = z ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [(Nat.coprime_zero_right _).mp hmn, pow_one, pow_zero] at h
    exact ⟨1, one_ne_zero, by rw [pow_zero, h]⟩
  · have hy : y ≠ 0 := fun hy ↦ pow_ne_zero m hx (by rw [h, hy, zero_pow hn])
    refine ⟨y ^ Int.gcdA m n * x ^ Int.gcdB m n,
      mul_ne_zero (zpow_ne_zero _ hy) (zpow_ne_zero _ hx), ?_⟩
    rw [mul_pow, ← zpow_natCast, zpow_comm, zpow_natCast, ← h, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hx, mul_comm _ (n : ℤ), ← Int.gcd_eq_gcd_ab,
      Int.gcd_natCast_natCast, hmn, Nat.cast_one, zpow_one]

end
