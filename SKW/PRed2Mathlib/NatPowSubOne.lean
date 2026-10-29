module

public import Mathlib.Data.Nat.GCD.Basic

set_option linter.style.header false

/-!
# PRed to Mathlib: `Nat.pow_sub_one_dvd_pow_sub_one_iff`

The declaration in this file was extracted from `SKW.Prereqs.Stickelberger` and submitted
upstream as Mathlib PR [#45464](https://github.com/leanprover-community/mathlib4/pull/45464),
where the variables are renamed `b` and `c`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted.
-/

@[expose] public section

/-- For `1 < a`, the number `a ^ m - 1` divides `a ^ n - 1` precisely when `m` divides `n`. -/
theorem Nat.pow_sub_one_dvd_pow_sub_one_iff {a : ℕ} (ha : 1 < a) {n m : ℕ} :
    a ^ m - 1 ∣ a ^ n - 1 ↔ m ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.pow_sub_one_mod_pow_sub_one, Nat.sub_eq_zero_iff_le,
    ← pow_zero a, Nat.pow_le_pow_iff_right ha, Nat.le_zero, Nat.dvd_iff_mod_eq_zero]
