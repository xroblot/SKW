module

public import Mathlib.NumberTheory.NumberField.Basic

set_option linter.style.header false

/-!
# PRed to Mathlib: `SMulCommClass G (𝓞 K) (𝓞 L)`

The instance in this file replaces `smul_eq_galRestrict_apply` in `SKW.Stickelberger.Stickelberger`
and was submitted upstream as Mathlib PR
[#46234](https://github.com/leanprover-community/mathlib4/pull/46234).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its imports should be deleted.
-/

@[expose] public section

open NumberField

instance {K L : Type*} [Field K] [Field L] [Algebra K L] {G : Type*} [Group G]
    [MulSemiringAction G L] [SMulCommClass G K L] : SMulCommClass G (𝓞 K) (𝓞 L) :=
  ⟨fun _ _ _ ↦ by
    simp_rw [RingOfIntegers.ext_iff, RingOfIntegers.coe_eq_algebraMap, Algebra.smul_def,
      algebraMap.smul', map_mul, smul_mul', ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K L, smul_algebraMap, algebraMap.smul']⟩
