/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.RamificationInertia.Basic

-- the only SKW dependency left: `Ideal.absNorm_eq_card`, used in `traceChar_apply_pow`.
-- Too small for a PR of its own, so it ships with this file when it goes upstream.
public import SKW.Prereqs.Ideals

/-!
# The additive character attached to the trace

Let `A` be a ring, `P` an ideal of `A` lying over the ideal `𝒑 = (p)` of `ℤ`, and `ζ` a primitive
`p`-th root of unity in a ring `R`. Composing the trace of `A ⧸ P` over `ℤ ⧸ 𝒑` with the character
of `ℤ ⧸ 𝒑 ≃ ZMod p` attached to `ζ` gives an additive character of `A ⧸ P` with values in `R`. This
file defines that character and establishes its basic properties: it is primitive when `P` is
maximal, it is invariant under the Frobenius, and it is compatible with extending the ring of
values.

## Main definitions

* `addCharTrace`: the additive character of `A ⧸ P` sending `x` to `ζ ^ Algebra.trace x`.

## Main results

* `exists_nat_traceChar_eq_pow`: the value of `addCharTrace` at `x` is `ζ ^ a` for any natural
  number `a` representing the trace of `x`; this is how the character is computed in practice.

* `isPrimitive_traceChar`: over a maximal ideal, `addCharTrace` is primitive.

* `traceChar_apply_pow`: `addCharTrace` is invariant under the Frobenius `x ↦ x ^ p`.

* `compAddChar_traceChar`: pushing `addCharTrace` along an algebra homomorphism `R → S` gives the
  character attached to the image of `ζ`.

## Tags

additive character, trace

-/

public section

open Ideal

variable {p : ℕ} [NeZero p] {A R : Type*} [CommRing A] [CommRing R] (P : Ideal A)

local notation3 "𝒑" => span {(p : ℤ)}

variable {ζ : R} (hζ : IsPrimitiveRoot ζ p)

attribute [local instance] Ideal.Quotient.field

/-- The additive character of `A ⧸ P` sending `x` to `ζ ^ Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x`,
where `ζ` is a primitive `p`-th root of unity and `P` lies over `𝒑 = (p)`. -/
noncomputable def addCharTrace [P.LiesOver 𝒑] : AddChar (A ⧸ P) R :=
  (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom  <|
    AddMonoidHom.comp (Int.quotientSpanNatEquivZMod p) (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸
      P)).toAddMonoidHom

theorem traceChar_apply [P.LiesOver 𝒑] (x : A ⧸ P) :
    addCharTrace P hζ x =
      ζ ^ (Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)).val := by rfl

/-- The value of `addCharTrace` at `x` is `ζ ^ a` for any natural number `a` representing the
trace of `x`. -/
theorem exists_nat_traceChar_eq_pow [P.LiesOver 𝒑] (x : A ⧸ P) :
    ∃ a : ℕ, addCharTrace P hζ x = ζ ^ a ∧ Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x = a := by
  refine ⟨(Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x)).val, rfl, ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk 𝒑), ← Int.quotientSpanNatEquivZMod_comp_castRingHom p,
    RingHom.comp_apply, map_natCast]
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, RingHom.coe_coe, RingEquiv.symm_apply_apply]

theorem traceChar_apply_eq_one_iff [P.LiesOver 𝒑] {x : A ⧸ P} :
    addCharTrace P hζ x = 1 ↔ Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x = 0 := by
  rw [traceChar_apply, ← orderOf_dvd_iff_pow_eq_one, ← hζ.eq_orderOf, ← ZMod.natCast_eq_zero_iff,
    ZMod.natCast_zmod_val, RingEquiv.map_eq_zero_iff]

theorem traceChar_ne_one [𝒑.IsMaximal] [P.IsMaximal] [P.LiesOver 𝒑]
    [FiniteDimensional (ℤ ⧸ 𝒑) (A ⧸ P)] :
    addCharTrace P hζ ≠ 1 := by
  refine AddChar.ne_one_iff.mpr ?_
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp <| Algebra.trace_ne_zero (ℤ ⧸ 𝒑) (A ⧸ P)
  exact ⟨x, by rwa [ne_eq, traceChar_apply_eq_one_iff]⟩

/-- Over a maximal ideal, `addCharTrace` is primitive, that is `mulShift` by a nonzero element is
nontrivial. -/
theorem isPrimitive_traceChar [𝒑.IsMaximal] [P.IsMaximal] [P.LiesOver 𝒑]
    [FiniteDimensional (ℤ ⧸ 𝒑) (A ⧸ P)] :
    AddChar.IsPrimitive (addCharTrace P hζ) :=
  AddChar.IsPrimitive.of_ne_one (traceChar_ne_one P hζ)

/-- `addCharTrace` is invariant under the Frobenius `x ↦ x ^ p` of `A ⧸ P`. -/
theorem traceChar_apply_pow [Fact (p.Prime)] [P.LiesOver 𝒑] [P.IsMaximal] [Finite (A ⧸ P)]
    (x : A ⧸ P) :
    addCharTrace P hζ (x ^ p) = addCharTrace P hζ x := by
  have : CharP (A ⧸ P) p := ringChar.of_eq <| by
    rw [Ideal.ringChar_quot, ← over_def P 𝒑, Ideal.absNorm_eq_card, Int.card_ideal_quot]
  have : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite (ℤ ⧸ 𝒑)
  have : x ^ p = FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) (A ⧸ P) p x := by
    rw [FiniteField.frobeniusAlgEquiv_apply, ← Nat.card_eq_fintype_card, Int.card_ideal_quot]
  rw [this, traceChar_apply, Algebra.trace_eq_of_algEquiv, traceChar_apply]

theorem addCharTrace_mk_eq_one [P.LiesOver 𝒑] {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A ⧸ P) :
    Ideal.Quotient.mk 𝓟 (addCharTrace P hζ x) = 1 := by
  rw [traceChar_apply, show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, Finset.sum_range_succ', pow_zero, Nat.choose_zero_right,
    Nat.cast_one, map_add, map_sum, map_mul, map_pow, map_one, map_natCast, add_eq_right]
  exact Finset.sum_eq_zero fun x hx ↦ by
    rw [Quotient.eq_zero_iff_mem.mpr h, zero_pow x.succ_ne_zero, zero_mul]

include hζ in
theorem addCharTrace_mk_sq_eq [P.LiesOver 𝒑] {𝓟 : Ideal R} [(𝓟 ^ 2).LiesOver 𝒑] (h : ζ - 1 ∈ 𝓟)
    (x : A ⧸ P) :
    Ideal.Quotient.mk (𝓟 ^ 2) (addCharTrace P hζ x) =
      1 + Algebra.trace (ℤ ⧸ 𝒑) (A ⧸ P) x • (Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1)) := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow P hζ x
  rw [ha, ha', show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, map_sum, map_mul, map_natCast, sub_add_cancel, Algebra.smul_def]
  cases a
  · simp
  · simp only [Finset.sum_range_succ', zero_add, pow_one, Nat.choose_one_right, Nat.cast_add,
      Nat.cast_one, pow_zero, Nat.choose_zero_right, mul_one]
    rw [Finset.sum_eq_zero fun x _ ↦ ?_, zero_add, map_one, add_comm, mul_comm]
    rw [Quotient.eq_zero_iff_mem.mpr, zero_mul]
    rw [add_assoc, pow_add]
    exact Ideal.mul_mem_left _ _ <| Submodule.pow_mem_pow 𝓟 h 2

/-- Pushing `addCharTrace` along an algebra homomorphism `R → S` gives the character attached to
the image of `ζ`. -/
theorem compAddChar_traceChar [P.LiesOver 𝒑] {S : Type*} [CommRing S] [Algebra R S]
    [FaithfulSMul R S] :
    (algebraMap R S).compAddChar (addCharTrace P hζ) =
        addCharTrace P (hζ.map_of_injective (FaithfulSMul.algebraMap_injective R S)) := by
  ext x
  have hζ₀ := hζ.map_of_injective (FaithfulSMul.algebraMap_injective R S)
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow P hζ x
  obtain ⟨b, hb, hb'⟩ := exists_nat_traceChar_eq_pow P hζ₀ x
  simp_rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_ofClass,
    Function.comp_apply, ha, hb, map_pow]
  refine (hζ₀.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq.mpr ?_
  rwa [hb', CharP.natCast_eq_natCast, Int.ringChar_idealQuot, hζ₀.eq_orderOf, Nat.ModEq.comm] at ha'

theorem monoidHom_comp_addCharTrace_eq_mulShift [P.LiesOver 𝒑] {F : Type*} [FunLike F R R]
    [MonoidHomClass F R R] (f : F) (n : ℕ) (h : f ζ = ζ ^ n) (x) :
    f (addCharTrace P hζ x) = (addCharTrace P hζ).mulShift n x := by
  rw [AddChar.mulShift_apply]
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow P hζ x
  obtain ⟨b, hb, hb'⟩ := exists_nat_traceChar_eq_pow P hζ (n * x)
  have : n * a % p = b % p := by
    suffices (n * a : ℤ ⧸ 𝒑) = b by
      rwa [← Nat.cast_mul, CharP.natCast_eq_natCast, Int.ringChar_idealQuot] at this
    rw [← ha', ← hb', ← smul_eq_mul, ← map_smul, Algebra.smul_def]
    simp
  rw [ha, hb, map_pow, h, ← pow_mul, ← pow_mod_orderOf _ (n * a), ← pow_mod_orderOf _ b,
    ← hζ.eq_orderOf, this]
