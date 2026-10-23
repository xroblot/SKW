module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

set_option linter.style.header false

/-!
# PRed to Mathlib: when is `ζ - 1` a unit

The declarations in this file were extracted from `SKW.Prereqs.CyclotomicField` and submitted
upstream as Mathlib PR [#45220](https://github.com/leanprover-community/mathlib4/pull/45220), to
`Mathlib/RingTheory/Polynomial/Cyclotomic/Eval.lean`. There
`IsPrimitiveRoot.isUnit_sub_one_iff_isUnit_eval_cyclotomic` is renamed
`isUnit_sub_one_iff_isUnit_eval_one_cyclotomic` and takes `[NeZero n]` instead of `1 < n`, and the
primitive root `hζ` comes first in all four `IsPrimitiveRoot` lemmas.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
(and its import in `SKW.Prereqs.CyclotomicField`) should be deleted, and any usages redirected to
the Mathlib versions.
-/

@[expose] public section

/-- The `n`-th cyclotomic polynomial takes the value `1` at `1` when `n` is neither `1` nor a prime
power. -/
theorem Polynomial.eval_one_cyclotomic_not_isPrimePow {R : Type*} [Ring R] {n : ℕ} (hn : n ≠ 1)
    (h : ¬ IsPrimePow n) : Polynomial.eval 1 (Polynomial.cyclotomic n R) = 1 := by
  refine eval_one_cyclotomic_not_prime_pow fun {p} hp k hk ↦ ?_
  obtain rfl | hk₀ := Nat.eq_zero_or_pos k
  · exact hn (by simpa using hk.symm)
  · exact h ⟨p, k, hp.prime, hk₀, hk⟩

open Polynomial in
/-- The element `ζ - 1` is a unit precisely when the `n`-th cyclotomic polynomial takes a unit
value at `1`. -/
theorem IsPrimitiveRoot.isUnit_sub_one_iff_isUnit_eval_cyclotomic {R : Type*} [CommRing R]
    [IsDomain R] {n : ℕ}
    (hn : 1 < n) {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    IsUnit (ζ - 1) ↔ IsUnit (eval 1 (cyclotomic n R)) := by
  have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have : Nonempty (primitiveRoots n R) := ⟨ζ, by rwa [mem_primitiveRoots (NeZero.pos _)]⟩
  have h_unit {η : R} (hη : η ∈ primitiveRoots n R) : IsUnit (1 - η) ↔ IsUnit (ζ - 1) := by
    obtain ⟨i, -, hi, rfl⟩ := hζ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
    apply Associated.isUnit_iff
    rw [← Associated.neg_left_iff, neg_sub]
    exact (hζ.associated_sub_one_pow_sub_one_of_coprime hi).symm
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ]
  simp +contextual [eval_prod, h_unit]

open Polynomial in
/-- If the order of `ζ` is not a prime power, then `ζ - 1` is a unit. -/
theorem IsPrimitiveRoot.isUnit_sub_one_of_not_isPrimePow {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (hn : 1 < n) (hn' : ¬ IsPrimePow n) {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    IsUnit (ζ - 1) := by
  rw [hζ.isUnit_sub_one_iff_isUnit_eval_cyclotomic hn,
    eval_one_cyclotomic_not_isPrimePow hn.ne' hn']
  exact isUnit_one

open Polynomial in
/-- If the order of `ζ` is a power of the prime `p`, then `ζ - 1` is a unit precisely when `p` is
one. -/
theorem IsPrimitiveRoot.isUnit_sub_one_iff_of_prime_pow {R : Type*} [CommRing R] [IsDomain R]
    {p k : ℕ} [hp : Fact p.Prime] {ζ : R} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    IsUnit (ζ - 1) ↔ IsUnit (p : R) := by
  rw [hζ.isUnit_sub_one_iff_isUnit_eval_cyclotomic (Nat.one_lt_pow (by lia) hp.out.one_lt),
    eval_one_cyclotomic_prime_pow]

open Polynomial in
/-- The element `ζ - 1` is a unit precisely when the order `n` of `ζ` is not a prime power. -/
theorem IsPrimitiveRoot.isUnit_sub_one_iff {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalHom (algebraMap ℤ R)] {n : ℕ} (hn : 1 < n) {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    IsUnit (ζ - 1) ↔ ¬ IsPrimePow n := by
  refine ⟨fun h hpp ↦ ?_, hζ.isUnit_sub_one_of_not_isPrimePow hn⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have : Fact p.Prime := ⟨hp⟩
  rw [hζ.isUnit_sub_one_iff_of_prime_pow, show (p : R) = algebraMap ℤ R p by push_cast; ring,
    isUnit_map_iff, Int.isUnit_iff] at h
  have := hp.two_le
  obtain h | h := h <;> lia
