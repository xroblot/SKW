module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.Algebra.GroupWithZero.Torsion

@[expose] public section

/-!
# PRed to Mathlib: `FractionalIdeal.spanSingletonHom` / `FractionalIdeal.isMulTorsionFree_of_le_nonZeroDivisors`

The declarations in this file were extracted from `SKW.Prereqs.FractionalIdeal` and submitted
upstream as Mathlib PR [#40636](https://github.com/leanprover-community/mathlib4/pull/40636).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.FractionalIdeal`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

open FractionalIdeal nonZeroDivisors

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]
  [IsLocalization S P]

@[simps]
def FractionalIdeal.spanSingletonHom :
    P →* FractionalIdeal S P where
  toFun x := spanSingleton S x
  map_one' := spanSingleton_one
  map_mul' x y := (spanSingleton_mul_spanSingleton x y).symm

/-- If the ideal monoid of `R` is torsion-free and `S ≤ R⁰`, then the monoid of fractional
ideals of `R` (localized at `S`) is also torsion-free. -/
theorem FractionalIdeal.isMulTorsionFree_of_le_nonZeroDivisors (h : S ≤ R⁰) [IsMulTorsionFree (Ideal R)] :
    IsMulTorsionFree (FractionalIdeal S P) where
  pow_left_injective {n} hn I J hIJ := by
    let a := algebraMap R P I.den
    let b := algebraMap R P J.den
    suffices spanSingleton S (a * b) * I = spanSingleton S (a * b) * J by
      refine IsUnit.mul_left_cancel ?_ this
      rw [← spanSingleton_mul_spanSingleton]
      exact ((IsLocalization.map_units _ I.den).map spanSingletonHom).mul <|
        (IsLocalization.map_units _ J.den).map spanSingletonHom
    have main : Ideal.span {J.den.val} * I.num = Ideal.span {I.den.val} * J.num := by
      dsimp at hIJ
      rw [← (IsMulTorsionFree.pow_left_injective hn).eq_iff, ← coeIdeal_inj' (P := P) h]
      simp only [mul_pow, coeIdeal_mul, coeIdeal_pow, coeIdeal_span_singleton]
      rw [← den_mul_self_eq_num', mul_pow, hIJ,  ← mul_assoc, mul_right_comm,
        ← mul_pow, den_mul_self_eq_num', mul_comm]
    calc spanSingleton S (a * b) * I
        = spanSingleton S a * spanSingleton S b * I := by rw [← spanSingleton_mul_spanSingleton]
      _ = spanSingleton S b * (spanSingleton S a * I) := by ring
      _ = spanSingleton S b * ↑(I.num) := by rw [I.den_mul_self_eq_num']
      _ = ↑(Ideal.span {(J.den : R)} * I.num) := by rw [← coeIdeal_span_singleton, ← coeIdeal_mul]
      _ = ↑(Ideal.span {(I.den : R)} * J.num) := by rw [main]
      _ = spanSingleton S a * ↑(J.num) := by rw [coeIdeal_mul, coeIdeal_span_singleton]
      _ = spanSingleton S a * (spanSingleton S b * J) := by rw [J.den_mul_self_eq_num']
      _ = spanSingleton S a * spanSingleton S b * J := by ring
      _ = spanSingleton S (a * b) * J := by rw [spanSingleton_mul_spanSingleton]

instance [IsLocalization R⁰ P] [IsMulTorsionFree (Ideal R)] :
    IsMulTorsionFree (FractionalIdeal R⁰ P) :=
  FractionalIdeal.isMulTorsionFree_of_le_nonZeroDivisors le_rfl

end
