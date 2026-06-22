module

public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

instance NumberField.sup {E F : Type*} [Field E] [Field F] [Algebra E F] (K L : IntermediateField E F)
    [NumberField K] [NumberField L] :
    NumberField ↑(K ⊔ L) :=
  haveI : CharZero E := (algebraMap E K).charZero
  { to_charZero := IntermediateField.charZero (K ⊔ L)
    to_finiteDimensional := by
      have : FiniteDimensional ℚ E := Module.Finite.left ℚ E K
      have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
      have : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
      exact FiniteDimensional.trans ℚ E _ }

instance NumberField.inf {E F : Type*} [Field E] [Field F] [Algebra E F] (K L : IntermediateField E F)
    [NumberField K] [NumberField L] :
    NumberField ↑(K ⊓ L) :=
  haveI : CharZero E := (algebraMap E K).charZero
  { to_charZero := IntermediateField.charZero (K ⊓ L)
    to_finiteDimensional := Module.Finite.left ℚ _ K }
