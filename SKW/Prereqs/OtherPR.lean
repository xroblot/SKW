module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification

@[expose] public section

open NumberField

theorem Ideal.ramificationIdx_sup_eq_one {L : Type*} [Field L] [NumberField L]
    {F₁ F₂ : IntermediateField ℚ L} (htop : F₁ ⊔ F₂ = ⊤) {p : Ideal ℤ} {P₁ : Ideal (𝓞 F₁)}
    {P₂ : Ideal (𝓞 F₂)} {P : Ideal (𝓞 L)} [P₁.LiesOver p] [P₂.LiesOver p]
    [P.LiesOver P₁] [P.LiesOver P₂] (h₁ : ramificationIdx p P₁ = 1)
    (h₂ : ramificationIdx p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx p P = 1 := by
  sorry
