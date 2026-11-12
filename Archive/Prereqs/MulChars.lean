module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.GaussSum

public import SKW.Prereqs.Stickelberger

set_option linter.style.header false


@[expose] public section

/-! ### AddChar / MonoidHom.compAddChar -/

@[simp]
theorem MonoidHom.compAddChar_one {A M : Type*} [AddMonoid A] [Monoid M] {N : Type*}
    [Monoid N] (f : M →* N) :
    f.compAddChar (1 : AddChar A M) = 1 := by
  ext; simp

theorem MonoidHom.compAddChar_eq_one_iff {A M : Type*} [AddMonoid A] [Monoid M] {N : Type*}
    [Monoid N] {f : M →* N} (hf : Function.Injective f) {φ : AddChar A M} :
    f.compAddChar φ = 1 ↔ φ = 1 := by
  rw [← MonoidHom.compAddChar_one f, (f.compAddChar_injective_right hf).eq_iff]

/-! ### MulChar -/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
-- TODO(SKW): upstream both into `Mathlib/NumberTheory/MulChar/Basic.lean`, next to
-- `MulChar.apply_ne_zero_iff`, which is the same statement with `≠ 0` in place of `IsUnit`;
-- Mathlib currently writes `ha.isUnit.map χ` by hand, as in `MulChar/Lemmas.lean:186`.
/-- A multiplicative character sends a unit to a unit. -/
theorem MulChar.isUnit_apply {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    (χ : MulChar R R') {a : R} (ha : IsUnit a) :
    IsUnit (χ a) :=
  ha.map χ
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
/-- A value of a multiplicative character is a unit precisely at a unit. -/
@[simp]
theorem MulChar.isUnit_apply_iff {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    [Nontrivial R'] {χ : MulChar R R'} {a : R} :
    IsUnit (χ a) ↔ IsUnit a := by
  refine ⟨fun h ↦ ?_, χ.isUnit_apply⟩
  contrapose h
  rw [map_nonunit χ h]
  exact not_isUnit_zero
-/
