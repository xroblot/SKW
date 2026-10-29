module

public import Mathlib.FieldTheory.Finite.Basic

set_option linter.style.header false

/-!
# PRed to Mathlib: sums of powers over a finite field

The declarations in this file were extracted from `SKW.Prereqs.Stickelberger` and
`SKW.Prereqs.NumberTheory`, and submitted upstream as Mathlib PR
[#45465](https://github.com/leanprover-community/mathlib4/pull/45465). There `sum_pow` is renamed
`sum_pow_of_ne_zero`, and the proof of `sum_pow_lt_card_sub_one'` replaces the one of
`FiniteField.sum_pow_lt_card_sub_one`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted, and the usages redirected:
`FiniteField.sum_pow` to `FiniteField.sum_pow_of_ne_zero` and
`FiniteField.sum_pow_lt_card_sub_one'` to `FiniteField.sum_pow_lt_card_sub_one`.
-/

@[expose] public section

namespace FiniteField

open Finset

variable (K : Type*) [Field K] [Fintype K]

local notation "q" => Fintype.card K

/-- A sum over the nonzero elements of a finite field is a sum over its units. -/
theorem sum_sdiff_zero {M : Type*} [AddCommMonoid M] [DecidableEq K] (f : K → M) :
    ∑ x ∈ univ \ {0}, f x = ∑ x : Kˣ, f x := by
  let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
  have : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  simp [← this, univ.sum_map φ, φ]

/-- The sum of `x ^ i`, with `i ≠ 0`, as `x` ranges over a finite field of cardinality `q`
is equal to `-1` if `q - 1 ∣ i`, and to `0` otherwise. -/
theorem sum_pow (i : ℕ) (hi : i ≠ 0) :
    ∑ x : K, x ^ i = if q - 1 ∣ i then -1 else 0 := by
  classical
  rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hi, add_zero,
    sum_sdiff_zero, sum_pow_units K i]

/-- The sum of all the elements of a finite field of cardinality `q` is equal to `1` if `q = 2`,
and to `0` otherwise. -/
theorem sum_univ_id_eq_ite :
    ∑ x : K, x = if q = 2 then 1 else 0 := by
  rw [show ∑ x : K, x = ∑ x : K, x ^ 1 by simp, sum_pow K 1 one_ne_zero]
  simp only [Nat.dvd_one, Nat.pred_eq_succ_iff, zero_add]
  split_ifs with hq
  · rw [neg_eq_iff_add_eq_zero]
    exact_mod_cast hq ▸ cast_card_eq_zero K
  · rfl

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
theorem sum_pow_lt_card_sub_one' (i : ℕ) (h : i < q - 1) : ∑ x : K, x ^ i = 0 := by
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [sum_pow K _ hi, ite_eq_right]
  contrapose! h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h

end FiniteField
