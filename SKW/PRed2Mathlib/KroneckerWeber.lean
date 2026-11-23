module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option linter.style.header false

/-!
# PRed to Mathlib: endomorphisms of a free module of rank one, Galois extensions of `ℚ`

The declarations in this file were extracted from `SKW.Prereqs.KroneckerWeber` and submitted
upstream as two Mathlib PRs.

* The `LinearMap` and `LinearEquiv` lemmas are in
  [#46317](https://github.com/leanprover-community/mathlib4/pull/46317). There
  `LinearMap.det_eq_one_iff_eq_id` is renamed `LinearMap.det_eq_one_iff_eq_id_of_finrank_eq_one`,
  and the `LinearMap` lemmas no longer assume `StrongRankCondition`.
* The `NumberField` lemmas are replaced in
  [#46384](https://github.com/leanprover-community/mathlib4/pull/46384) by
  `NumberField.isTotallyReal_or_isTotallyComplex`.

Once a PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, its part of
this file should be deleted and the usages redirected to the Mathlib versions. When the file is
empty, delete it and its import in `SKW.Prereqs.KroneckerWeber`.
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

namespace NumberField
open InfinitePlace
variable {K : Type*} [Field K] [Algebra ℚ K] [IsGalois ℚ K]

theorem InfinitePlace.isReal_of_isGalois {w : InfinitePlace K} (hw : w.IsReal)
    (w' : InfinitePlace K) :
    w'.IsReal := by
  obtain ⟨σ, rfl⟩ : ∃ σ, σ • w = w' := exists_smul_eq_of_comap_eq (k := ℚ) (Subsingleton.elim _ _)
  exact isReal_smul_iff.mpr hw

theorem isTotallyComplex_iff_exists_isComplex [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ∃ w : InfinitePlace K, w.IsComplex := by
  refine ⟨fun h ↦ ⟨Classical.arbitrary _, h.isComplex _⟩, fun ⟨w, hw⟩ ↦ ⟨fun w' ↦ ?_⟩⟩
  exact not_isReal_iff_isComplex.mp fun h ↦ not_isReal_iff_isComplex.mpr hw (isReal_of_isGalois h w)

theorem isTotallyComplex_iff_not_isTotallyReal [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ¬ IsTotallyReal K := by
  simp_rw [isTotallyComplex_iff_exists_isComplex, isTotallyReal_iff, not_forall,
    not_isReal_iff_isComplex]

theorem isTotallyReal_iff_not_isTotallyComplex [Nonempty (InfinitePlace K)] :
    IsTotallyReal K ↔ ¬ IsTotallyComplex K := by
  rw [isTotallyComplex_iff_not_isTotallyReal, not_not]
end NumberField
