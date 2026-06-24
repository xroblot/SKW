module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

open Module

@[simp]
theorem LinearEquiv.smul_id_of_finrank_eq_one_symm_apply {R : Type*} [CommRing R]
    [StrongRankCondition R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (d1 : Module.finrank R M = 1) (u : M →ₗ[R] M) :
    (smul_id_of_finrank_eq_one d1).symm u = u.det := by
  obtain ⟨c, rfl, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 u
  rw [map_smul, LinearMap.det_smul, d1, pow_one, LinearMap.det_id, mul_one,
    show LinearMap.id = (1 : R) • LinearMap.id by rw [one_smul],
    ← smul_id_of_finrank_eq_one_apply d1, symm_apply_apply, smul_eq_mul, mul_one]

theorem LinearMap.det_eq_one_iff_eq_id {R : Type*} [CommRing R] [StrongRankCondition R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Free R M] (d1 : Module.finrank R M = 1) (u : M →ₗ[R] M) :
    u.det = 1 ↔ u = id := by
  rw [← LinearEquiv.smul_id_of_finrank_eq_one_symm_apply d1, LinearEquiv.symm_apply_eq,
    LinearEquiv.smul_id_of_finrank_eq_one_apply, one_smul]

theorem finrank_eq_of_equiv_equiv {R R' M M₁ : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Semiring R'] [AddCommMonoid M₁] [Module R' M₁] (i : R → R') (j : M ≃+ M₁)
    (hi : Function.Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.finrank R M = Module.finrank R' M₁ := by
  simpa using! congr_arg Cardinal.toNat <| lift_rank_eq_of_equiv_equiv i j hi hc
