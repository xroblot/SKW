module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.GaussSum
public import SKW.PRed2Mathlib.MulChars


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
