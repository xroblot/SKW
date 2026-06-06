module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.Adjoin.PowerBasis

@[expose] public section

open IntermediateField
/-- Version of `PowerBasis.ofAdjoinEqTop` for `IntermediateField.adjoin`. -/
noncomputable def PowerBasis.ofAdjoinSimpleEqTop {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] {α : L} (h : IsIntegral K α) (hgen : K⟮α⟯ = ⊤) : PowerBasis K L :=
  PowerBasis.ofAdjoinEqTop h (by
    have h := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h.isAlgebraic
    rw [hgen, IntermediateField.top_toSubalgebra] at h
    exact h.symm)

@[simp]
lemma PowerBasis.ofAdjoinSimpleEqTop_gen {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] {α : L} (h : IsIntegral K α) (hgen : K⟮α⟯ = ⊤) :
    (PowerBasis.ofAdjoinSimpleEqTop h hgen).gen = α := by
  simp [PowerBasis.ofAdjoinSimpleEqTop, PowerBasis.ofAdjoinEqTop_gen]

@[simp]
lemma PowerBasis.ofAdjoinSimpleEqTop_dim {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] {α : L} (h : IsIntegral K α) (hgen : K⟮α⟯ = ⊤) :
    (PowerBasis.ofAdjoinSimpleEqTop h hgen).dim = (minpoly K α).natDegree := by
  simp [PowerBasis.ofAdjoinSimpleEqTop, PowerBasis.ofAdjoinEqTop_dim]

/-!
# Generalizations of Mathlib.FieldTheory.KummerExtension

This file contains lemmas that generalize or complement results in Mathlib's
`KummerExtension` file, intended for eventual upstreaming.
-/

/-- An arbitrary choice of `ⁿ√a` in a field where `Xⁿ - a` splits. Generalizes
`rootOfSplitsXPowSubC` which requires `IsSplittingField`. -/
noncomputable def rootOfSplitsXPowSubC' {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (a : K)
    {L : Type*} [Field L] [Algebra K L]
    (h : ((Polynomial.X ^ n - Polynomial.C a).map (algebraMap K L)).Splits) : L :=
  Polynomial.rootOfSplits h
    (by simp [Polynomial.degree_X_pow_sub_C hn, hn.ne'])

/-- The `n`-th power of `rootOfSplitsXPowSubC'` equals `algebraMap K L a`. Generalizes
`rootOfSplitsXPowSubC_pow` which requires `IsSplittingField`. -/
lemma rootOfSplitsXPowSubC_pow' {K : Type*} [Field K] {n : ℕ} [NeZero n] (a : K)
    {L : Type*} [Field L] [Algebra K L]
    (h : ((Polynomial.X ^ n - Polynomial.C a).map (algebraMap K L)).Splits) :
    rootOfSplitsXPowSubC' (NeZero.pos n) a h ^ n = algebraMap K L a := by
  have hd : ((Polynomial.X ^ n - Polynomial.C a).map (algebraMap K L)).degree ≠ 0 := by
    simp [Polynomial.degree_X_pow_sub_C (NeZero.pos n), NeZero.ne n]
  have := Polynomial.eval_rootOfSplits h hd
  simp only [rootOfSplitsXPowSubC', Polynomial.eval_map, Polynomial.eval₂_sub,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at this ⊢
  exact this

/-- `rootOfSplitsXPowSubC` is a special case of `rootOfSplitsXPowSubC'` when `L` is a
splitting field. -/
lemma rootOfSplitsXPowSubC_eq {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (a : K)
    (L : Type*) [Field L] [Algebra K L] [Polynomial.IsSplittingField K L
      (Polynomial.X ^ n - Polynomial.C a)] :
    rootOfSplitsXPowSubC hn a L =
      rootOfSplitsXPowSubC' hn a (Polynomial.IsSplittingField.splits L _) := rfl

/-- `rootOfSplitsXPowSubC_pow` is a special case of `rootOfSplitsXPowSubC_pow'` when `L` is a
splitting field. -/
lemma rootOfSplitsXPowSubC_pow_eq {K : Type*} [Field K] {n : ℕ} [NeZero n] (a : K)
    (L : Type*) [Field L] [Algebra K L] [Polynomial.IsSplittingField K L
      (Polynomial.X ^ n - Polynomial.C a)] :
    rootOfSplitsXPowSubC (NeZero.pos n) a L ^ n = algebraMap K L a := by
  rw [rootOfSplitsXPowSubC_eq]
  exact rootOfSplitsXPowSubC_pow' a _

section

open Polynomial IntermediateField

/-- If `ζ` is a primitive `n`-th root of unity and `x ^ n = α ^ n`, then `x = ζ ^ j * α`
for some `j < n`. Generalizes the implicit content of `IsPrimitiveRoot.nthRoots_eq`. -/
lemma IsPrimitiveRoot.eq_pow_mul_of_pow_eq {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} [NeZero n] {ζ α x : R}
    (hζ : IsPrimitiveRoot ζ n) (h : x ^ n = α ^ n) :
    ∃ j : ℕ, j < n ∧ x = ζ ^ j * α := by
  have hx : x ∈ nthRoots n (α ^ n) := (mem_nthRoots (NeZero.pos n)).mpr h
  simp only [hζ.nthRoots_eq rfl, Multiset.mem_map, Multiset.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, hj, rfl⟩

/-- Kummer group characterization: let `K` be a field with a primitive `n`-th root of unity `ζ`,
`a ∈ K×` with `X ^ n - a` irreducible, `α` a root of `X ^ n - a` in `L = K(α)`, and
`σ ∈ Gal(L/K)` the automorphism defined by `σ(α) = ζ * α`.
If `β ∈ L` satisfies `β ^ n ∈ K×`, then `β = λ * α ^ j` for some `λ ∈ K` and `j < n`.

Proof: `σ(β)^n = β^n` (as `β^n ∈ K`), so `σ(β) = ζ^j * β` for some `j` (primitivity of `ζ`).
Writing `β = Σ k_i α^i` in the basis `{1, α, ..., α^{n-1}}`, comparing `σ(β) = Σ k_i ζ^i α^i`
with `ζ^j * β = Σ k_i ζ^j α^i` and using linear independence gives `k_i = 0` for `i ≠ j`. -/
theorem exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap {K : Type*} [Field K] {n : ℕ} [NeZero n]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {L : Type*} [Field L] [Algebra K L] {a : K}
    (hIrr : Irreducible (X ^ n - C a)) [IsSplittingField K L (X ^ n - C a)] {α : L}
    (hα : α ^ n = algebraMap K L a) (hgen : K⟮α⟯ = ⊤) {σ : L ≃ₐ[K] L} (hσ : σ α = algebraMap K L ζ * α)
    {β : L} {b : K} (hβ : β ^ n = algebraMap K L b) :
    ∃ (c : K) (j : ℕ), j < n ∧ β = algebraMap K L c * α ^ j := by
  classical
  have hmp : minpoly K α = X ^ n - C a :=
    (minpoly.eq_of_irreducible_of_monic hIrr (by simp [hα]) (monic_X_pow_sub_C a (NeZero.ne n))).symm
  have hint : IsIntegral K α := ⟨X ^ n - C a, monic_X_pow_sub_C a (NeZero.ne n), hmp ▸ minpoly.aeval K α⟩
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n := hζ.map_of_injective (algebraMap K L).injective
  have hσβn : (σ β) ^ n = β ^ n := by rw [← map_pow, hβ, AlgEquiv.commutes]
  obtain ⟨j, hj, hσβ⟩ := hζL.eq_pow_mul_of_pow_eq hσβn
  let B := PowerBasis.ofAdjoinSimpleEqTop hint hgen
  have hsB {i} : σ (B.basis i) = algebraMap K L ζ ^ i.val * (B.basis i) := by
    simp [PowerBasis.coe_basis, B, hσ, mul_pow]
  have hdB : B.dim = n := by rw [PowerBasis.ofAdjoinSimpleEqTop_dim, hmp, natDegree_X_pow_sub_C]
  let j₀ : Fin B.dim := ⟨j, by rwa [hdB]⟩
  refine ⟨B.basis.equivFun β j₀, j, hj, ?_⟩
  have h₀ := B.basis.sum_equivFun β
  nth_rewrite 1 [← h₀]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have {i} (hi : i ∈ Finset.univ.erase j₀) : B.basis.equivFun β i = 0 := by
    have h₁ := (congr_arg σ h₀).trans hσβ
    nth_rewrite 2 [← h₀] at h₁
    simp_rw [map_sum, map_smul, hsB] at h₁
    rw [Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
    simp_rw [Algebra.smul_def, ← mul_assoc, ← map_pow, ← map_mul, ← sub_mul, ← map_sub,
      ← Algebra.smul_def, mul_comm, ← sub_mul] at h₁
    have := linearIndependent_iff'.mp B.basis.linearIndependent _ _ h₁ i (Finset.mem_univ i)
    rwa [mul_eq_zero_iff_left] at this
    contrapose! hi
    simpa [j₀, Fin.ext_iff] using hζ.pow_inj (Fin.val_lt_of_le i hdB.le) hj (sub_eq_zero.mp hi)
  simp +contextual [j₀, this, Algebra.smul_def, B]

variable {F : Type*} [Field F] {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra K F]
  [IsGalois K F] {μ : F} {Ω : Type*} [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower K F Ω]

/-- A Kummer extension `Ω = F(ⁿ√μ)` (with `X ^ n - μ` irreducible over `F` and `char(F) ∤ n`)
is Galois over `K` if and only if for every `σ ∈ Gal(F/K)` there exist `ξ ∈ F` and `a : ℤ`
such that `σ(μ) = ξⁿ * μ^a`. -/
lemma isGalois_iff_forall_apply_eq_pow_mul_zpow (hμ : μ ≠ 0) (hn : (n : F) ≠ 0)
    (hF : (primitiveRoots n F).Nonempty) (hIrr : Irreducible (X ^ n - C μ))
    (hΩ : IsSplittingField F Ω (X ^ n - C μ)) :
    (∀ σ : F ≃ₐ[K] F, ∃ (ξ : F) (a : ℤ), σ μ = ξ ^ n * μ ^ a) ↔ IsGalois K Ω := by
  refine ⟨fun h ↦ ?_, ?_⟩
  ·
    sorry
  · intro h σ
    let τ := σ.liftNormal Ω
    let α := rootOfSplitsXPowSubC (NeZero.pos n) μ Ω
    have hα : α ^ n = algebraMap F Ω μ := rootOfSplitsXPowSubC_pow μ Ω
    have := congr_arg τ hα
    rw [AlgEquiv.liftNormal_commutes, map_pow] at this
    sorry

end

end
