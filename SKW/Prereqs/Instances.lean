module

public import SKW.Prereqs.IntermediateField

@[expose] public section

/-! ### Local instances

Instances we want available throughout the SKW development but are not (yet) sure belong in Mathlib.
Kept in one place so they are easy to review, promote, or drop. -/

open IntermediateField

/-- `lift E` is a number field whenever `E` is, transported along `liftAlgEquiv E : E ≃ₐ[K] lift E`. -/
instance IntermediateField.numberField_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} (E : IntermediateField K F) [NumberField E] :
    NumberField (lift E) :=
  .of_ringEquiv E (lift E) (liftAlgEquiv E).toRingEquiv

/-- `lift E` is Galois over the base field whenever `E` is. -/
instance IntermediateField.isGalois_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} (E : IntermediateField K F) [IsGalois K E] :
    IsGalois K (lift E) :=
  IsGalois.of_algEquiv (liftAlgEquiv E)

/-- `Gal(lift E / K)` is cyclic whenever `Gal(E / K)` is, via the isomorphism of Galois groups
induced by `liftAlgEquiv E`. -/
instance IntermediateField.isCyclic_gal_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} (E : IntermediateField K F) [IsCyclic Gal(E/K)] :
    IsCyclic Gal(lift E/K) :=
  (AlgEquiv.autCongr (liftAlgEquiv E)).isCyclic.mp ‹_›
