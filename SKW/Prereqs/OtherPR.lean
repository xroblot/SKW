module

public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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
theorem NumberField.isFundamentalDiscr_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  sorry

/-- An integer is odd iff it is not divisible by `2`. From Mathlib PR
[#43088](https://github.com/leanprover-community/mathlib4/pull/43088), where it is added to
`Mathlib/Algebra/Ring/Int/Parity.lean`. -/
theorem Int.not_two_dvd_iff_odd {n : ℤ} : ¬ 2 ∣ n ↔ Odd n := by grind
