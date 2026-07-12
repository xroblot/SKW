module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

@[expose] public section

open NumberField Ideal

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
