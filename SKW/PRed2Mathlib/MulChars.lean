module

public import Mathlib.NumberTheory.MulChar.Basic

@[expose] public section

/-!
# PRed to Mathlib: `MulChar.ringHomCompHom` / `MulChar.ringHomComp_zpow` / `MulChar.zpow_apply_coe`

The declarations in this file were extracted from `SKW.Prereqs.MulChars` and submitted
upstream as Mathlib PR [#40331](https://github.com/leanprover-community/mathlib4/pull/40331).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.MulChars`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

theorem MulChar.ringHomComp_zpow {R : Type*} [CommMonoidWithZero R] {R' : Type*} [CommRing R'] {R'' : Type*}
    [CommRing R''] (χ : MulChar R R') (f : R' →+* R'') (n : ℤ) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [ringHomComp_pow]
  · simp [ringHomComp_pow, MulChar.ringHomComp_inv]

@[simps]
def MulChar.ringHomCompHom {R : Type*} [CommMonoid R] {R' : Type*} [CommRing R'] {R'' : Type*}
    [CommRing R''] (f : R' →+* R'') : MulChar R R' →* MulChar R R'' where
  toFun χ := MulChar.ringHomComp χ f
  map_one' := by rw [ringHomComp_one]
  map_mul' _ _ := MulChar.ringHomComp_mul _ _ f

theorem MulChar.zpow_apply_coe_eq_apply_zpow {R : Type*} [CommGroupWithZero R] {R' : Type u_2}
    [CommMonoidWithZero R'] (χ : MulChar R R') (n : ℤ) (a : Rˣ) :
    (χ ^ n) a = χ (a ^ n : Rˣ) := by
  obtain ⟨n, (rfl | rfl)⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · rw [zpow_neg, zpow_natCast, inv_apply', ← Units.val_inv_eq_inv_val, pow_apply_coe, ← inv_zpow',
      zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

end
