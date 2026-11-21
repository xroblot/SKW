module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free

set_option linter.style.header false

/-!
# PRed to Mathlib: endomorphisms of a free module of rank one

The declarations in this file were extracted from `SKW.Prereqs.KroneckerWeber` and submitted
upstream as Mathlib PR [#46317](https://github.com/leanprover-community/mathlib4/pull/46317).
There `LinearMap.det_eq_one_iff_eq_id` is renamed
`LinearMap.det_eq_one_iff_eq_id_of_finrank_eq_one`, and the `LinearMap` lemmas no longer assume
`StrongRankCondition`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.KroneckerWeber` should be deleted, and the usages redirected to the
Mathlib versions.
-/

@[expose] public section

theorem LinearMap.apply_eq_det_smul_of_finrank_eq_one {R : Type*} [CommRing R]
    [StrongRankCondition R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (d1 : Module.finrank R M = 1) (u : M →ₗ[R] M) (x : M) :
    u x = u.det • x := by
  obtain ⟨c, rfl, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 u
  simp [LinearMap.det_smul, d1, pow_one]

theorem LinearEquiv.smul_id_of_finrank_eq_one_symm_apply {R : Type*} [CommRing R]
    [StrongRankCondition R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (d1 : Module.finrank R M = 1) (u : M →ₗ[R] M) :
    (smul_id_of_finrank_eq_one d1).symm u = u.det := by
  have : u = u.det • LinearMap.id := by
    ext x
    exact (LinearMap.apply_eq_det_smul_of_finrank_eq_one d1 u x)
  nth_rewrite 1 [this]
  rw [← smul_id_of_finrank_eq_one_apply d1, symm_apply_apply]

theorem LinearMap.det_eq_one_iff_eq_id {R : Type*} [CommRing R] [StrongRankCondition R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Free R M] (d1 : Module.finrank R M = 1) (u : M →ₗ[R] M) :
    u.det = 1 ↔ u = id := by
  rw [← LinearEquiv.smul_id_of_finrank_eq_one_symm_apply d1, LinearEquiv.symm_apply_eq,
    LinearEquiv.smul_id_of_finrank_eq_one_apply, one_smul]
