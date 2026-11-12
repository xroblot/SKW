module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

public import SKW.Prereqs.KroneckerWeber

set_option linter.style.header false

@[expose] public section

-- Copied to `SKW.Prereqs.KroneckerWeber`.
/-
instance NumberField.sup {E F : Type*} [Field E] [Field F] [Algebra E F] (K L : IntermediateField E
  F)
    [NumberField K] [NumberField L] :
    NumberField ↑(K ⊔ L) :=
  haveI : CharZero E := (algebraMap E K).charZero
  { to_charZero := IntermediateField.charZero (K ⊔ L)
    to_finiteDimensional := by
      have : FiniteDimensional ℚ E := Module.Finite.left ℚ E K
      have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
      have : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
      exact FiniteDimensional.trans ℚ E _ }
-/

instance NumberField.inf {E F : Type*} [Field E] [Field F] [Algebra E F] (K L : IntermediateField E
  F)
    [NumberField K] :
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

-- Copied to `SKW.Prereqs.KroneckerWeber`.
/-
/-- The `ℤ`-algebra isomorphism `(𝓞 K) ≃ₐ[ℤ] (𝓞 L)` given by restricting a ring isomorphism
  `e : K ≃+* L` to `𝓞 K`. Unlike `RingOfIntegers.mapAlgEquiv`, whose base is `𝓞 k`, this has base
  `ℤ`, which is convenient when the natural common base of `K` and `L` is `ℚ` (as `𝓞 ℚ` is only
  isomorphic to, not equal to, `ℤ`). -/
def mapIntAlgEquiv (e : K ≃+* L) : (𝓞 K) ≃ₐ[ℤ] (𝓞 L) := (mapRingEquiv e).toIntAlgEquiv
-/

@[simp]
theorem mapIntAlgEquiv_apply (e : K ≃+* L) (x : 𝓞 K) : (mapIntAlgEquiv e x : L) = e (x : K) := rfl

@[simp]
theorem mapIntAlgEquiv_symm_apply (e : K ≃+* L) (x : 𝓞 L) :
    ((mapIntAlgEquiv e).symm x : K) = e.symm (x : L) := rfl

end NumberField.RingOfIntegers

namespace NumberField

open InfinitePlace

variable {K : Type*} [Field K] [Algebra ℚ K] [IsGalois ℚ K]

-- Copied to `SKW.Prereqs.KroneckerWeber`.
/-
theorem InfinitePlace.isReal_of_isGalois {w : InfinitePlace K} (hw : w.IsReal)
    (w' : InfinitePlace K) :
    w'.IsReal := by
  obtain ⟨σ, rfl⟩ : ∃ σ, σ • w = w' := exists_smul_eq_of_comap_eq (k := ℚ) (Subsingleton.elim _ _)
  exact isReal_smul_iff.mpr hw
-/

theorem InfinitePlace.isComplex_of_isGalois {w : InfinitePlace K} (hw : w.IsComplex)
    (w' : InfinitePlace K) :
    w'.IsComplex := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_comap_eq (k := ℚ) (w := w) (w' := w') (Subsingleton.elim _ _)
  exact isComplex_smul_iff.mpr hw

theorem isTotallyReal_iff_exists_isReal [Nonempty (InfinitePlace K)] :
    IsTotallyReal K ↔ ∃ w : InfinitePlace K, w.IsReal :=
  ⟨fun h ↦ ⟨Classical.arbitrary _, h.isReal _⟩, fun ⟨_, hw⟩ ↦ ⟨isReal_of_isGalois hw⟩⟩

-- Copied to `SKW.Prereqs.KroneckerWeber`.
/-
theorem isTotallyComplex_iff_exists_isComplex [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ∃ w : InfinitePlace K, w.IsComplex := by
  refine ⟨fun h ↦ ⟨Classical.arbitrary _, h.isComplex _⟩, fun ⟨w, hw⟩ ↦ ⟨fun w' ↦ ?_⟩⟩
  exact not_isReal_iff_isComplex.mp fun h ↦ not_isReal_iff_isComplex.mpr hw (isReal_of_isGalois h w)
-/

-- Copied to `SKW.Prereqs.KroneckerWeber`.
/-
theorem isTotallyComplex_iff_not_isTotallyReal [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ¬ IsTotallyReal K := by
  simp_rw [isTotallyComplex_iff_exists_isComplex, isTotallyReal_iff, not_forall,
    not_isReal_iff_isComplex]
-/

-- Copied to `SKW.Prereqs.KroneckerWeber`.
/-
theorem isTotallyReal_iff_not_isTotallyComplex [Nonempty (InfinitePlace K)] :
    IsTotallyReal K ↔ ¬ IsTotallyComplex K := by
  rw [isTotallyComplex_iff_not_isTotallyReal, not_not]
-/

end NumberField
