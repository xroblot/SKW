module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.Int

public import SKW.Misc

@[expose] public section

open Ideal

variable {p : ℕ} [NeZero p] {A R : Type*} [CommRing A] [CommRing R] (P : Ideal A)

local notation3 "𝒑" => span {(p : ℤ)}

variable {ζ : R} (hζ : IsPrimitiveRoot ζ p)

attribute [local instance] Ideal.Quotient.field

noncomputable def addCharTrace [P.LiesOver 𝒑] : AddChar (A ⧸ P) R :=
  (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom  <|
    AddMonoidHom.comp (Int.quotientSpanNatEquivZMod p) (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P)).toAddMonoidHom

theorem addCharTrace_apply [P.LiesOver 𝒑] (x : A ⧸ P) :
    addCharTrace P hζ x =
      ζ ^ (Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)).val := rfl

theorem addCharTrace_apply_eq_one_iff [P.LiesOver 𝒑] {x : A ⧸ P} :
    addCharTrace P hζ x = 1 ↔ Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x = 0 := by
  rw [addCharTrace_apply, ← orderOf_dvd_iff_pow_eq_one, ← hζ.eq_orderOf, ← ZMod.natCast_eq_zero_iff,
    ZMod.natCast_zmod_val, RingEquiv.map_eq_zero_iff]

theorem addCharTrace_ne_one [𝒑.IsMaximal] [P.IsMaximal] [P.LiesOver 𝒑]
    [FiniteDimensional (ℤ ⧸ 𝒑) (A ⧸ P)] :
    addCharTrace P hζ ≠ 1 := by
  refine AddChar.ne_one_iff.mpr ?_
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp <| Algebra.trace_ne_zero (ℤ ⧸ 𝒑) (A ⧸ P)
  exact ⟨x, by rwa [ne_eq, addCharTrace_apply_eq_one_iff]⟩

theorem addCharTrace_isPrimitive [𝒑.IsMaximal] [P.IsMaximal] [P.LiesOver 𝒑]
    [FiniteDimensional (ℤ ⧸ 𝒑) (A ⧸ P)] :
    AddChar.IsPrimitive (addCharTrace P hζ) :=
  AddChar.IsPrimitive.of_ne_one (addCharTrace_ne_one P hζ)

theorem addCharTrace_frob_apply [Fact (p.Prime)] [P.LiesOver 𝒑] [P.IsMaximal] [Finite (A ⧸ P)]
    (x : A ⧸ P) :
    addCharTrace P hζ (x ^ p) = addCharTrace P hζ x := by
  have : CharP (A ⧸ P) p := ringChar.of_eq <| by
    rw [Ideal.ringChar_quot, ← over_def P 𝒑, Ideal.absNorm_eq_card, Int.card_ideal_quot]
  have : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite (ℤ ⧸ 𝒑)
  have : x ^ p = FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) (A ⧸ P) p x := by
    rw [FiniteField.frobeniusAlgEquiv_apply, ← Nat.card_eq_fintype_card, Int.card_ideal_quot]
  rw [this, addCharTrace_apply, Algebra.trace_eq_of_algEquiv, addCharTrace_apply]

theorem addCharTrace_mk_eq_one [P.LiesOver 𝒑] {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A ⧸ P) :
    Ideal.Quotient.mk 𝓟 (addCharTrace P hζ x) = 1 := by
  rw [addCharTrace_apply, show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, Finset.sum_range_succ', pow_zero, Nat.choose_zero_right,
    Nat.cast_one, map_add, map_sum, map_mul, map_pow, map_one, map_natCast, add_eq_right]
  exact Finset.sum_eq_zero fun x hx ↦ by
    rw [Quotient.eq_zero_iff_mem.mpr h, zero_pow x.succ_ne_zero, zero_mul]

include hζ in
theorem addCharTrace_mk_sq_eq [P.LiesOver 𝒑] {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A ⧸ P) :
    Ideal.Quotient.mk (𝓟 ^ 2) (addCharTrace P hζ x) =
      1 + ((Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)).val : R ⧸ 𝓟 ^ 2) *
        (Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1)) := by
  rw [addCharTrace_apply, show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, map_sum, map_mul, map_natCast, sub_add_cancel]
  cases ((Int.quotientSpanNatEquivZMod p) ((Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P)) x)).val
  · simp
  · simp only [Finset.sum_range_succ', zero_add, pow_one, Nat.choose_one_right, Nat.cast_add,
      Nat.cast_one, pow_zero, Nat.choose_zero_right, mul_one]
    rw [Finset.sum_eq_zero fun x _ ↦ ?_, zero_add, add_comm, mul_comm, map_one]
    rw [Quotient.eq_zero_iff_mem.mpr, zero_mul]
    rw [add_assoc, pow_add]
    exact Ideal.mul_mem_left _ _ <| Submodule.pow_mem_pow 𝓟 h 2
