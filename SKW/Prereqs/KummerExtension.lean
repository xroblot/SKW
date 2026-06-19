module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import SKW.Prereqs.Normal
public import SKW.PRed2Mathlib.KummerExtension
public import SKW.Prereqs.AlgebraMisc

@[expose] public section

open IntermediateField Polynomial

/-!
# Generalizations of Mathlib.FieldTheory.KummerExtension

This file contains lemmas that generalize or complement results in Mathlib's
`KummerExtension` file, intended for eventual upstreaming.
-/

-- /-- An arbitrary choice of `ⁿ√a` in a field where `Xⁿ - a` splits. Generalizes
-- `rootOfSplitsXPowSubC` which requires `IsSplittingField`. -/
-- noncomputable def rootOfSplitsXPowSubC' {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (a : K)
--     {L : Type*} [Field L] [Algebra K L]
--     (h : ((Polynomial.X ^ n - Polynomial.C a).map (algebraMap K L)).Splits) : L :=
--   Polynomial.rootOfSplits h
--     (by simp [Polynomial.degree_X_pow_sub_C hn, hn.ne'])

-- /-- The `n`-th power of `rootOfSplitsXPowSubC'` equals `algebraMap K L a`. Generalizes
-- `rootOfSplitsXPowSubC_pow` which requires `IsSplittingField`. -/
-- lemma rootOfSplitsXPowSubC_pow' {K : Type*} [Field K] {n : ℕ} [NeZero n] (a : K)
--     {L : Type*} [Field L] [Algebra K L]
--     (h : ((Polynomial.X ^ n - Polynomial.C a).map (algebraMap K L)).Splits) :
--     rootOfSplitsXPowSubC' (NeZero.pos n) a h ^ n = algebraMap K L a := by
--   have hd : ((Polynomial.X ^ n - Polynomial.C a).map (algebraMap K L)).degree ≠ 0 := by
--     simp [Polynomial.degree_X_pow_sub_C (NeZero.pos n), NeZero.ne n]
--   have := Polynomial.eval_rootOfSplits h hd
--   simp only [rootOfSplitsXPowSubC', Polynomial.eval_map, Polynomial.eval₂_sub,
--     Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at this ⊢
--   exact this

-- /-- `rootOfSplitsXPowSubC` is a special case of `rootOfSplitsXPowSubC'` when `L` is a
-- splitting field. -/
-- lemma rootOfSplitsXPowSubC_eq {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (a : K)
--     (L : Type*) [Field L] [Algebra K L] [Polynomial.IsSplittingField K L
--       (Polynomial.X ^ n - Polynomial.C a)] :
--     rootOfSplitsXPowSubC hn a L =
--       rootOfSplitsXPowSubC' hn a (Polynomial.IsSplittingField.splits L _) := rfl

-- /-- `rootOfSplitsXPowSubC_pow` is a special case of `rootOfSplitsXPowSubC_pow'` when `L` is a
-- splitting field. -/
-- lemma rootOfSplitsXPowSubC_pow_eq {K : Type*} [Field K] {n : ℕ} [NeZero n] (a : K)
--     (L : Type*) [Field L] [Algebra K L] [Polynomial.IsSplittingField K L
--       (Polynomial.X ^ n - Polynomial.C a)] :
--     rootOfSplitsXPowSubC (NeZero.pos n) a L ^ n = algebraMap K L a := by
--   rw [rootOfSplitsXPowSubC_eq]
--   exact rootOfSplitsXPowSubC_pow' a _

open Polynomial in
theorem rootOfSplitsXPowSubC_minpoly {K : Type*} [Field K] {n : ℕ} [NeZero n] (a : K) (L : Type*)
    [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)] (H : Irreducible (X ^ n - C a)) :
    minpoly K (rootOfSplitsXPowSubC (NeZero.pos n) a L) = X ^ n - C a := by
  refine (minpoly.eq_of_irreducible_of_monic H ?_ (monic_X_pow_sub_C _ (NeZero.ne n))).symm
  rw [aeval_sub, aeval_X_pow, rootOfSplitsXPowSubC_pow, aeval_C, sub_eq_zero]

open Polynomial in
theorem rootOfSplitsXPowSubC_isIntegral {K : Type*} [Field K] {n : ℕ} [NeZero n] (a : K) (L : Type*)
    [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)] (H : Irreducible (X ^ n - C a)) :
    IsIntegral K (rootOfSplitsXPowSubC (NeZero.pos n) a L) := by
  rw [← minpoly.ne_zero_iff, rootOfSplitsXPowSubC_minpoly _ _ H]
  exact Irreducible.ne_zero H

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
`a ∈ Kˣ` with `X ^ n - a` irreducible, `α` a root of `X ^ n - a` in `L = K(α)`, and
`σ ∈ Gal(L/K)` the automorphism defined by `σ(α) = ζ * α`.
If `β ∈ L` satisfies `β ^ n ∈ Kˣ`, then `β = λ * α ^ j` for some `λ ∈ K` and `j < n`. -/
theorem exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap {K : Type*} [Field K] {n : ℕ} [NeZero n]
    (hK : (primitiveRoots n K).Nonempty) {L : Type*} [Field L] [Algebra K L] {a : K}
    (hIrr : Irreducible (X ^ n - C a)) [IsSplittingField K L (X ^ n - C a)] {α : L}
    (hα : α ^ n = algebraMap K L a) {β : L} {b : K} (hβ : β ^ n = algebraMap K L b) :
    ∃ (c : K) (j : ℕ), j < n ∧ β = algebraMap K L c * α ^ j := by
  classical
  have hmp : minpoly K α = X ^ n - C a :=
    (minpoly.eq_of_irreducible_of_monic hIrr (by simp [hα]) (monic_X_pow_sub_C a (NeZero.ne n))).symm
  have hint : IsIntegral K α := ⟨X ^ n - C a, monic_X_pow_sub_C a (NeZero.ne n), hmp ▸ minpoly.aeval K α⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_root_eq_top_of_isSplittingField hK hIrr hα
  obtain ⟨ζ, hζ⟩ := hK
  replace hζ : IsPrimitiveRoot ζ n := isPrimitiveRoot_of_mem_primitiveRoots hζ
  let σ := (autEquivZmod hIrr L hζ).symm (Multiplicative.ofAdd 1)
  have hσ : σ α = algebraMap K L ζ * α := by
    have := autEquivZmod_symm_apply_natCast hIrr L hα hζ 1
    rwa [pow_one, Algebra.smul_def, Nat.cast_one] at this
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
  [IsGalois K F] {μ : F} {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]

-- /-- A Kummer extension `L = F(ⁿ√μ)` (with `X ^ n - μ` irreducible over `F` and `¬ char(F) ∣ n`)
-- is Galois over `K` if and only if for every `σ ∈ Gal(F/K)` there exist `ξ ∈ F` and `a : ℤ`
-- such that `σ(μ) = ξ ^ n * μ ^ a`. -/
-- lemma isGalois_iff_forall_apply_eq_pow_mul_zpow (hμ : μ ≠ 0) (hn : (n : F) ≠ 0)
--     [FiniteDimensional K F] (hF : (primitiveRoots n F).Nonempty) (hIrr : Irreducible (X ^ n - C μ))
--     (hL : IsSplittingField F L (X ^ n - C μ)) :
--     (∀ σ : F ≃ₐ[K] F, ∃ (ξ : F) (a : ℕ), σ μ = ξ ^ n * μ ^ a) ↔ IsGalois K L := by
--   let α := rootOfSplitsXPowSubC (NeZero.pos n) μ L
--   have hα : α ^ n = algebraMap F L μ := rootOfSplitsXPowSubC_pow μ L
--   refine ⟨fun h ↦ ?_, fun h σ ↦ ?_⟩
--   · refine { to_isSeparable := ?_, to_normal := ?_ }
--     · have : Algebra.IsSeparable F L :=
--         Algebra.isSeparable_of_separable_splitting_field (separable_X_pow_sub_C μ hn hμ)
--       exact Algebra.IsSeparable.trans K F L
--     · obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K F
--       have : adjoin K {algebraMap F L θ, α} = ⊤ := by
--         rw [← Set.singleton_union, adjoin_union, ← Set.image_singleton, ← IsScalarTower.coe_toAlgHom' K,
--           ← adjoin_map, hθ, ← AlgHom.fieldRange_eq_map, ← restrictScalars_adjoin_eq_sup,
--           IsScalarTower.adjoin_range_toAlgHom']
--         exact congr_arg (restrictScalars K ·) <| adjoin_root_eq_top_of_isSplittingField hF hIrr hα
--       refine Normal.of_adjoin_eq_top this fun x hx ↦ ?_
--       obtain rfl | rfl := hx
--       · refine ⟨(Algebra.IsIntegral.isIntegral θ).algebraMap, ?_⟩
--         rw [minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective F L) θ,
--           IsScalarTower.algebraMap_eq K F L, ← Polynomial.map_map]
--         exact Polynomial.Splits.map  (IsGalois.splits K θ) _
--       · refine ⟨?_, ?_⟩
--         · have : FiniteDimensional K L := by
--             have : FiniteDimensional F L := IsSplittingField.finiteDimensional L (X ^ n - C μ)
--             exact FiniteDimensional.trans K F L
--           exact Algebra.IsIntegral.isIntegral α
--         · rw [IsScalarTower.algebraMap_eq K F, ← Polynomial.map_map]
--           have := map_dvd (algebraMap F L) <| IsGalois.map_minpoly_dvd_prod_minpoly K F α
--           refine Polynomial.Splits.of_dvd ?_ ?_ this
--           · have := rootOfSplitsXPowSubC_minpoly μ L hIrr
--             rw [this]
--             simp
--             rw [Polynomial.map_prod]
--             apply Polynomial.Splits.prod
--             intro σ _
--             obtain ⟨ξ, a, h⟩ := h σ
--             rw [h]
--             simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
--             obtain ⟨ζ₀, hζ₀⟩ := hF
--             let ζ : L := algebraMap F L ζ₀
--             have hζ : IsPrimitiveRoot ζ n :=
--               (isPrimitiveRoot_of_mem_primitiveRoots hζ₀).map_of_injective
--                 (FaithfulSMul.algebraMap_injective F L)
--             refine X_pow_sub_C_splits_of_isPrimitiveRoot (α := (algebraMap F L) ξ * α ^ a) hζ ?_
--             rw [map_mul, map_pow, map_pow, ← hα, pow_right_comm, ← mul_pow]
--           · simp_rw [Polynomial.map_prod, Polynomial.map_map]
--             refine Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ?_
--             refine Polynomial.map_ne_zero ?_
--             refine minpoly.ne_zero ?_
--             exact rootOfSplitsXPowSubC_isIntegral μ L hIrr
--   · have hτα := congr_arg (σ.liftNormal L) hα
--     rw [AlgEquiv.liftNormal_commutes, map_pow] at hτα
--     obtain ⟨ξ, j, _, hj⟩ := exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap hF hIrr hα hτα
--     refine ⟨ξ, j, ?_⟩
--     apply FaithfulSMul.algebraMap_injective F L
--     rw [← hτα, hj, mul_pow, map_mul, map_pow, pow_right_comm, hα, map_pow]

open Module

omit [NeZero n] in
/-- If `α ^ n` lies in the base field `K` and `gcd t n = 1`, then `α ^ t` generates the same simple
extension over `K` as `α` (Bézout: `α = (α^t)ᵘ · (αⁿ)ᵛ` with `t·u + n·v = 1`). -/
theorem adjoin_simple_pow_of_coprime {α : L} {a : K} (hα : α ^ n = algebraMap K L a) {t : ℕ}
    (ht : t.Coprime n) : K⟮α ^ t⟯ = K⟮α⟯ := by
  refine le_antisymm (adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self K α) t)) ?_
  rw [adjoin_simple_le_iff]
  obtain rfl | hα0 := eq_or_ne α 0
  · exact zero_mem _
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr ht
  nth_rewrite 2 [← pow_one α]
  rw [← zpow_natCast _ 1, Nat.cast_one, ← huv, zpow_add₀ hα0, mul_comm u, mul_comm v, zpow_mul, zpow_mul,
    zpow_natCast, zpow_natCast]
  exact mul_mem (zpow_mem (mem_adjoin_simple_self K _) u) (hα ▸ zpow_mem (_root_.algebraMap_mem _ a) v)

theorem isSplittingField_X_pow_sub_C_pow_of_coprime (a : K) (hK : (primitiveRoots n K).Nonempty)
    (H : Irreducible (X ^ n - C a)) {t : ℕ} (ht : t.Coprime n)
    [hS : IsSplittingField K L (X ^ n - C a)] :
    IsSplittingField K L (X ^ n - C (a ^ t)) := by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L (X ^ n - C a)
  have hrank : finrank K L = n := finrank_of_isSplittingField_X_pow_sub_C hK H (L := L)
  set α := rootOfSplitsXPowSubC (NeZero.pos n) a L
  have hα : α ^ n = algebraMap K L a := rootOfSplitsXPowSubC_pow a L
  have hβ : (α ^ t) ^ n = algebraMap K L (a ^ t) := by rw [pow_right_comm, hα, map_pow]
  have htopβ : K⟮α ^ t⟯ = ⊤ := by
    rw [adjoin_simple_pow_of_coprime hα ht]
    exact IntermediateField.adjoin_root_eq_top_of_isSplittingField hK H hα
  rw [← hrank] at hK hβ ⊢
  exact isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK hβ htopβ

theorem isSplittingField_X_pow_sub_C_mul_pow (a : K) (hK : (primitiveRoots n K).Nonempty)
    (H : Irreducible (X ^ n - C a)) {x : K} (hx : x ≠ 0)
    [hS : IsSplittingField K L (X ^ n - C a)] :
    IsSplittingField K L (X ^ n - C (a * x ^ n)) := by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L (X ^ n - C a)
  let α := rootOfSplitsXPowSubC (NeZero.pos n) a L
  have hα : α ^ n = algebraMap K L a := rootOfSplitsXPowSubC_pow a L
  have hβ : (α * algebraMap K L x) ^ n = algebraMap K L (a * x ^ n) := by
    rw [mul_pow, hα, map_mul, map_pow]
  have hrank : finrank K L = n := finrank_of_isSplittingField_X_pow_sub_C hK H (L := L)
  rw [← hrank] at hK hβ H hα hS ⊢
  refine isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK hβ ?_
  rw [IntermediateField.adjoin_simple_mul α x hx]
  exact IntermediateField.adjoin_root_eq_top_of_isSplittingField hK H hα

end

end
