module

public import Mathlib.NumberTheory.MulChar.Basic

set_option linter.style.header false

/-!
# PRed to Mathlib: `MulChar.isUnit_apply` and `MulChar.isUnit_apply_iff`

The declarations in this file were extracted from `SKW.Prereqs.Stickelberger`. Upstream they are
replaced by an instance `IsLocalHom χ` for a multiplicative character `χ`, submitted as Mathlib PR
[#45463](https://github.com/leanprover-community/mathlib4/pull/45463).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted, and the usages redirected:
`MulChar.isUnit_apply` to `IsUnit.map` and `MulChar.isUnit_apply_iff` to `isUnit_map_iff`.
-/

@[expose] public section

/-- A multiplicative character sends a unit to a unit. -/
theorem MulChar.isUnit_apply {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    (χ : MulChar R R') {a : R} (ha : IsUnit a) :
    IsUnit (χ a) :=
  ha.map χ

/-- A value of a multiplicative character is a unit precisely at a unit. -/
@[simp]
theorem MulChar.isUnit_apply_iff {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    [Nontrivial R'] {χ : MulChar R R'} {a : R} :
    IsUnit (χ a) ↔ IsUnit a := by
  refine ⟨fun h ↦ ?_, χ.isUnit_apply⟩
  contrapose h
  rw [map_nonunit χ h]
  exact not_isUnit_zero
