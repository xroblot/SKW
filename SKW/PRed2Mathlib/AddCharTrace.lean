module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.Ideal.Int

set_option linter.style.header false

/-!
# PRed to Mathlib: the additive character attached to the trace

The declarations in this file were extracted from `SKW.Stickelberger.AddCharTrace` and submitted
upstream as Mathlib PR [#44545](https://github.com/leanprover-community/mathlib4/pull/44545), as
the new file `Mathlib/NumberTheory/AddCharacter/Trace.lean`. The upstream version takes the
carrier of the character as an explicit argument, so `traceChar hζ` here reads `traceChar A hζ`
there.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this
file and the shell `SKW.Stickelberger.AddCharTrace` that imports it should both be deleted, and
the usages in `SKW.Stickelberger.{GaussSum, Factorization, valGauss}` redirected to the Mathlib
versions.
-/

public section

open AddChar Ideal

variable {p : ℕ} [NeZero p] {A R F : Type*} [CommRing A] [CommRing R] [Field F]
  [Algebra (ℤ ⧸ (Ideal.span {(p : ℤ)})) A] [Algebra (ℤ ⧸ (Ideal.span {(p : ℤ)})) F]

local notation3 "𝒑" => Ideal.span {(p : ℤ)}

variable {ζ : R} (hζ : IsPrimitiveRoot ζ p)

attribute [local instance] Ideal.Quotient.field

namespace AddChar

/-- The additive character of `A` sending `x` to `ζ ^ Algebra.trace (ℤ ⧸ 𝒑) A x`, where `ζ` is a
primitive `p`-th root of unity. -/
noncomputable def traceChar : AddChar A R :=
  (zmodChar p hζ.pow_eq_one).compAddMonoidHom  <|
    AddMonoidHom.comp (Int.quotientSpanNatEquivZMod p) (Algebra.trace (ℤ ⧸ 𝒑) A).toAddMonoidHom

theorem traceChar_apply (x : A) :
    traceChar hζ x =
      ζ ^ (Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) A x)).val := by rfl

/-- The value of `traceChar` at `x` is `ζ ^ a` for any natural number `a` representing the
trace of `x`. This is easier to work with than `traceChar_apply in most cases. -/
theorem exists_nat_traceChar_eq_pow (x : A) :
    ∃ a : ℕ, traceChar hζ x = ζ ^ a ∧ Algebra.trace (ℤ ⧸ 𝒑) A x = a := by
  refine ⟨(Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) A x)).val, rfl, ?_⟩
  have := RingHom.congr_fun (Int.quotientSpanNatEquivZMod_comp_castRingHom p)
    (Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) A x)).val
  rwa [RingHom.comp_apply, eq_intCast, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id,
    RingHom.coe_coe, RingEquiv.symm_apply_apply] at this

theorem traceChar_apply_eq_one_iff {x : A} :
    traceChar hζ x = 1 ↔ Algebra.trace (ℤ ⧸ 𝒑) A x = 0 := by
  rw [traceChar_apply, ← orderOf_dvd_iff_pow_eq_one, ← hζ.eq_orderOf, ← ZMod.natCast_eq_zero_iff,
    ZMod.natCast_zmod_val, RingEquiv.map_eq_zero_iff]

theorem traceChar_ne_one [Fact (p.Prime)] [Finite F] :
    traceChar hζ ≠ (1 : AddChar F R) := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp <| Algebra.trace_ne_zero (ℤ ⧸ 𝒑) F
  exact ne_one_iff.mpr ⟨x, by rwa [ne_eq, traceChar_apply_eq_one_iff]⟩

/-- Over a finite field, the character `traceChar` is primitive. -/
theorem isPrimitive_traceChar [Fact (p.Prime)] [Finite F] :
    IsPrimitive (traceChar hζ : AddChar F R) :=
  IsPrimitive.of_ne_one (traceChar_ne_one hζ)

/-- Over a finite field, the character `traceChar` is invariant under the Frobenius
`x ↦ x ^ p`. -/
theorem traceChar_apply_pow [Fact (p.Prime)] [Finite F] (x : F) :
    traceChar hζ (x ^ p) = traceChar hζ x := by
  have : CharP F p :=
    (Algebra.charP_iff (ℤ ⧸ 𝒑) _ _).mp <| ringChar.of_eq <| Int.ringChar_idealQuot p
  have : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite (ℤ ⧸ 𝒑)
  have : x ^ p = FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) F p x := by
    rw [FiniteField.frobeniusAlgEquiv_apply, ← Nat.card_eq_fintype_card, Int.card_ideal_quot]
  rw [this, traceChar_apply, Algebra.trace_eq_of_algEquiv, traceChar_apply]

theorem mk_traceChar_apply_eq_one {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A) :
    Ideal.Quotient.mk 𝓟 (traceChar hζ x) = 1 := by
  rw [traceChar_apply, show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, Finset.sum_range_succ', pow_zero, Nat.choose_zero_right,
    Nat.cast_one, map_add, map_sum, map_mul, map_pow, map_one, map_natCast, add_eq_right]
  exact Finset.sum_eq_zero fun x hx ↦ by
    rw [Quotient.eq_zero_iff_mem.mpr h, zero_pow x.succ_ne_zero, zero_mul]

include hζ in
theorem mk_traceChar_apply_eq_one_add_smul {𝓟 : Ideal R} [(𝓟 ^ 2).LiesOver 𝒑] (h : ζ - 1 ∈ 𝓟)
    (x : A) :
    Ideal.Quotient.mk (𝓟 ^ 2) (traceChar hζ x) =
      1 + Algebra.trace (ℤ ⧸ 𝒑) A x • (Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1)) := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow hζ x
  rw [ha, ha', show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, map_sum, map_mul, map_natCast, sub_add_cancel, Algebra.smul_def]
  cases a
  · simp
  · have {k} : Ideal.Quotient.mk (𝓟 ^ 2) ((ζ - 1) ^ (k + 2)) = 0 :=
      Quotient.eq_zero_iff_mem.mpr <| pow_le_pow_right le_add_self <| pow_mem_pow h _
    simp only [Finset.sum_range_succ', zero_add, pow_one, Nat.choose_one_right, Nat.cast_add,
      Nat.cast_one, pow_zero, Nat.choose_zero_right, mul_one, this, zero_mul, Finset.sum_const_zero,
      map_sub, map_one, zero_add]
    ring

/-- Pushing `traceChar` along an algebra homomorphism `R → S` gives the character attached to
the image of `ζ`. -/
theorem compAddChar_traceChar {S : Type*} [CommRing S] [Algebra R S] [FaithfulSMul R S] :
    (algebraMap R S).compAddChar (traceChar hζ : AddChar A R) =
        traceChar (hζ.map_of_injective (FaithfulSMul.algebraMap_injective R S)) := by
  ext x
  have hζ' := hζ.map_of_injective (FaithfulSMul.algebraMap_injective R S)
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow hζ x
  obtain ⟨b, hb, hb'⟩ := exists_nat_traceChar_eq_pow hζ' x
  rw [MonoidHom.coe_compAddChar, Function.comp_apply, ha, hb, map_pow, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, (hζ'.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq]
  rwa [hb', CharP.natCast_eq_natCast, Int.ringChar_idealQuot, hζ'.eq_orderOf, Nat.ModEq.comm] at ha'

/-- If an homomorphism of `R` sends `ζ` to `ζ ^ n`, then it sends the value of
`traceChar` at `x` to the value at `x` of the shift of `traceChar` by `n`. -/
theorem map_traceChar_apply_eq_mulShift {G : Type*} [FunLike G R R]
    [MonoidHomClass G R R] (f : G) (n : ℕ) (h : f ζ = ζ ^ n) (x) :
    f (traceChar hζ x) = (traceChar hζ).mulShift (n : A) x := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow hζ x
  obtain ⟨b, hb, hb'⟩ := exists_nat_traceChar_eq_pow hζ (n * x)
  rw [AddChar.mulShift_apply, ha, hb, map_pow, h, ← pow_mul,
    (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
  rwa [← nsmul_eq_mul, map_nsmul, ha', nsmul_eq_mul, ← Nat.cast_mul, CharP.natCast_eq_natCast,
    Int.ringChar_idealQuot] at hb'

end AddChar
