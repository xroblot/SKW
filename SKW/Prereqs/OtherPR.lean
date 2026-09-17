module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

open NumberField Ideal IntermediateField

theorem Ideal.ramificationIdx_sup_eq_one {L : Type*} [Field L] [NumberField L]
    {F₁ F₂ : IntermediateField ℚ L} (htop : F₁ ⊔ F₂ = ⊤) {p : Ideal ℤ} {P₁ : Ideal (𝓞 F₁)}
    {P₂ : Ideal (𝓞 F₂)} {P : Ideal (𝓞 L)} [P₁.LiesOver p] [P₂.LiesOver p]
    [P.LiesOver P₁] [P.LiesOver P₂] (h₁ : ramificationIdx P₁ ℤ = 1)
    (h₂ : ramificationIdx P₂ ℤ = 1) (hp : p ≠ ⊥) :
    ramificationIdx P ℤ = 1 := by
  sorry

theorem IsInertiaField.ramificationIdx_eq (K L : Type*) {A B : Type*} [Field K] [Field L]
    [Algebra K L] [CommRing A] [CommRing B] [MulSemiringAction Gal(L/K) B] (E 𝓞E : Type*)
    [Field E] [CommRing 𝓞E] [Algebra E L] (P : Ideal B) (𝓟E : Ideal 𝓞E) [Algebra A 𝓞E]
    [IsInertiaField K L P E] [Algebra 𝓞E B] [P.LiesOver 𝓟E] :
    ramificationIdx 𝓟E A = 1 := by
  sorry

/-- In an abelian Galois number field `L/ℚ`, the inertia field of a prime `𝔔` lying over the rational
prime `q` is unramified at `q` (the inertia field is Galois here, so unramifiedness holds at every
prime over `q`, not just the one below `𝔔`). Extracted from the inertia-field API of Mathlib PR
[#36733](https://github.com/leanprover-community/mathlib4/pull/36733). -/
theorem isUnramifiedIn_fixedField_inertia {L : Type*} [Field L] [NumberField L]
    [IsAbelianGalois ℚ L] {q : ℕ} (𝔔 : Ideal (𝓞 L)) [𝔔.IsPrime]
    [𝔔.LiesOver (span {(q : ℤ)})] :
    Algebra.IsUnramifiedIn (𝓞 ↥(fixedField (inertia Gal(L/ℚ) 𝔔))) (span {(q : ℤ)}) := by
  sorry

/-- The discriminant of a quadratic field is a fundamental discriminant. Extracted from the
quadratic-fields stack, where it is stated for `[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.isFundamentalDiscr_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  sorry

/-- An integer is odd iff it is not divisible by `2`. From Mathlib PR
[#43088](https://github.com/leanprover-community/mathlib4/pull/43088), where it is added to
`Mathlib/Algebra/Ring/Int/Parity.lean`. -/
theorem Int.not_two_dvd_iff_odd {n : ℤ} : ¬ 2 ∣ n ↔ Odd n := by grind

/-- Every quadratic field is `ℚ(√(discr K))`. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.nonempty_algEquiv_quadraticAlgebra_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (NumberField.discr K : ℚ) 0) := by
  sorry

/-- The discriminant is a complete invariant of quadratic fields. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.nonempty_algEquiv_iff_discr_eq (K F : Type*) [Field K] [Field F]
    [NumberField K] [NumberField F] (hK : Module.finrank ℚ K = 2)
    (hF : Module.finrank ℚ F = 2) :
    Nonempty (K ≃ₐ[ℚ] F) ↔ NumberField.discr K = NumberField.discr F := by
  sorry

/-- The discriminant of `ℚ(√d)` is `4 * d` when `d` is squarefree and `d ≡ 2, 3 [ZMOD 4]`. From
Mathlib PR [#43491](https://github.com/leanprover-community/mathlib4/pull/43491). -/
theorem NumberField.QuadraticField.discr_sqrtd {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]
    [NumberField (QuadraticAlgebra ℚ (d : ℚ) 0)]
    (hd₁ : Squarefree d) (hd₂ : d % 4 = 2 ∨ d % 4 = 3) :
    NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) = 4 * d := by
  sorry

/-- The discriminant of `ℚ(√d)` is `d` itself when `d` is squarefree and `d ≡ 1 [ZMOD 4]`. From
Mathlib PR [#43491](https://github.com/leanprover-community/mathlib4/pull/43491). -/
theorem NumberField.QuadraticField.discr_half {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]
    [NumberField (QuadraticAlgebra ℚ (d : ℚ) 0)]
    (hd : Squarefree d) (hd1 : d ≠ 1) (h : d % 4 = 1) :
    NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0) = d := by
  sorry

/-- `√(discr K)` lies in `K`. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.exists_sq_eq_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ∃ x : K, x ^ 2 = (NumberField.discr K : K) := by
  sorry

/-- The discriminant of a quadratic field is not a square. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.not_isSquare_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ¬ IsSquare (NumberField.discr K) := by
  sorry

/-- A quadratic field is totally real iff its discriminant is positive. From Mathlib PR
[#43493](https://github.com/leanprover-community/mathlib4/pull/43493), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.isTotallyReal_iff_discr_pos (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    IsTotallyReal K ↔ 0 < NumberField.discr K := by
  sorry

/-- Every fundamental discriminant other than `1` is the discriminant of a quadratic field. From
Mathlib PR [#43491](https://github.com/leanprover-community/mathlib4/pull/43491). -/
theorem NumberField.QuadraticField.discr_quadraticAlgebra {D : ℤ} [Fact (¬ IsSquare (D : ℚ))]
    [NumberField (QuadraticAlgebra ℚ (D : ℚ) 0)]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) :
    NumberField.discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D := by
  sorry

/-- Instance form of `NumberField.QuadraticField.isTotallyReal_iff_discr_pos`: a totally real
quadratic field has positive discriminant. -/
theorem NumberField.QuadraticField.discr_pos (K : Type*) [Field K] [NumberField K]
    [IsTotallyReal K] (hK : Module.finrank ℚ K = 2) :
    0 < NumberField.discr K :=
  (isTotallyReal_iff_discr_pos K hK).mp ‹_›
