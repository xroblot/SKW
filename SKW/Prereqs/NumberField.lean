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

open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K L : Type*} [Field K] [Field L]

/-- The `ℤ`-algebra homomorphism `(𝓞 K) →ₐ[ℤ] (𝓞 L)` given by restricting a ring homomorphism
  `f : K →+* L` to `𝓞 K`. Unlike `RingOfIntegers.mapAlgHom`, whose base is `𝓞 k`, this has base
  `ℤ`, which is convenient when the natural common base of `K` and `L` is `ℚ` (as `𝓞 ℚ` is only
  isomorphic to, not equal to, `ℤ`). -/
def mapIntAlgHom (f : K →+* L) : (𝓞 K) →ₐ[ℤ] (𝓞 L) := (mapRingHom f).toIntAlgHom

@[simp]
theorem mapIntAlgHom_apply (f : K →+* L) (x : 𝓞 K) : (mapIntAlgHom f x : L) = f (x : K) := rfl

/-- The `ℤ`-algebra isomorphism `(𝓞 K) ≃ₐ[ℤ] (𝓞 L)` given by restricting a ring isomorphism
  `e : K ≃+* L` to `𝓞 K`. Unlike `RingOfIntegers.mapAlgEquiv`, whose base is `𝓞 k`, this has base
  `ℤ`, which is convenient when the natural common base of `K` and `L` is `ℚ` (as `𝓞 ℚ` is only
  isomorphic to, not equal to, `ℤ`).

  Remark: the `commutes'` field is inlined to keep this self-contained; once
  `RingEquiv.toIntAlgEquiv` (Mathlib PR #40298) is available it can be golfed to
  `(mapRingEquiv e).toIntAlgEquiv`. -/
def mapIntAlgEquiv (e : K ≃+* L) : (𝓞 K) ≃ₐ[ℤ] (𝓞 L) :=
  { mapRingEquiv e with commutes' := fun _ => by simp }

@[simp]
theorem mapIntAlgEquiv_apply (e : K ≃+* L) (x : 𝓞 K) : (mapIntAlgEquiv e x : L) = e (x : K) := rfl

@[simp]
theorem mapIntAlgEquiv_symm_apply (e : K ≃+* L) (x : 𝓞 L) :
    ((mapIntAlgEquiv e).symm x : K) = e.symm (x : L) := rfl

end NumberField.RingOfIntegers
