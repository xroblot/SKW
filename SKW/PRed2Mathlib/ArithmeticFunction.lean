module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option linter.style.header false

/-!
# PRed to Mathlib: Euler's totient as an arithmetic function

The declarations in this file were extracted from `SKW.Prereqs.Stickelberger` and submitted
upstream as Mathlib PR [#46097](https://github.com/leanprover-community/mathlib4/pull/46097).
There `ArithmeticFunction.totient` takes values in `ℕ` instead of `ℤ`, and
`Nat.totient_lcm_mul_totient_gcd` is a direct consequence of `isMultiplicative_totient`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted, and the usages redirected to the
Mathlib versions.
-/

public section


/-- Euler's totient function as an arithmetic function with values in `ℤ`. -/
@[expose] def ArithmeticFunction.totient : ArithmeticFunction ℤ where
  toFun n := Nat.totient n
  map_zero' := by simp

@[simp]
theorem ArithmeticFunction.totient_apply (n : ℕ) :
    totient n = Nat.totient n := rfl

open Nat in
theorem ArithmeticFunction.isMultiplicative_totient :
    IsMultiplicative totient :=
  IsMultiplicative.iff_ne_zero.mpr ⟨by simp, fun _ _ h ↦ by simp [Nat.totient_mul h]⟩

theorem Nat.totient_lcm_mul_totient_gcd (m n : ℕ) :
    totient (lcm m n) * totient (gcd m n) = totient m * totient n := by
  have :=  ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply
    ArithmeticFunction.isMultiplicative_totient (x := m) (y := n)
  rwa [ArithmeticFunction.totient_apply, ArithmeticFunction.totient_apply,
    ArithmeticFunction.totient_apply, ArithmeticFunction.totient_apply, ← Nat.cast_mul,
    ← Nat.cast_mul, Nat.cast_inj] at this
