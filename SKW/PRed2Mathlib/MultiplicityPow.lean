module

public import Mathlib.RingTheory.Multiplicity

set_option linter.style.header false

/-!
# PRed to Mathlib: `multiplicity_pow` without finiteness hypothesis

The declarations in this file were extracted from `SKW.Prereqs.AlgebraMisc` and submitted
upstream as Mathlib PR [#45473](https://github.com/leanprover-community/mathlib4/pull/45473),
where `FiniteMultiplicity.congr_right` is renamed `Associated.finiteMultiplicity_iff_right` and
`multiplicity_pow` replaces `FiniteMultiplicity.multiplicity_pow` (now deprecated).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.AlgebraMisc` should be deleted, and the uses of
`FiniteMultiplicity.multiplicity_pow` in `SKW.KroneckerWeber.Basic` redirected to
`multiplicity_pow`.
-/

@[expose] public section

/-- Finiteness of the multiplicity passes to a divisor. -/
theorem FiniteMultiplicity.of_dvd {α : Type*} [Monoid α] {p a b : α} (hab : a ∣ b) :
    FiniteMultiplicity p b → FiniteMultiplicity p a :=
  fun ⟨n, hn⟩ ↦ ⟨n, fun h ↦ hn (h.trans hab)⟩

/-- Finiteness of the multiplicity in a nonzero power passes to the base. -/
theorem FiniteMultiplicity.of_pow {α : Type*} [Monoid α] {p a : α} {k : ℕ} (hk : k ≠ 0) :
    FiniteMultiplicity p (a ^ k) → FiniteMultiplicity p a :=
  of_dvd (dvd_pow_self a hk)

/-- Finiteness of the multiplicity only depends on the associate class of the second argument. -/
theorem FiniteMultiplicity.congr_right {α : Type*} [Monoid α] {p a b : α} (h : Associated a b) :
    FiniteMultiplicity p a ↔ FiniteMultiplicity p b :=
  ⟨of_dvd h.symm.dvd, of_dvd h.dvd⟩

/-- The multiplicity of a prime in a power, with no finiteness hypothesis. -/
theorem multiplicity_pow {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α] {p a : α}
    (hp : Prime p) {k : ℕ} :
    multiplicity p (a ^ k) = k * multiplicity p a := by
  by_cases h : FiniteMultiplicity p a
  · exact h.multiplicity_pow hp
  obtain rfl | hk := eq_or_ne k 0
  · simp
  · rw [multiplicity_eq_zero_of_not_finiteMultiplicity h, mul_zero,
      multiplicity_eq_zero_of_not_finiteMultiplicity fun h' ↦ h (h'.of_pow hk)]
