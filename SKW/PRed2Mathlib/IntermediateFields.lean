module

public import Mathlib.FieldTheory.IntermediateField.Algebraic

@[expose] public section

/-!
# PRed to Mathlib: `IntermediateField.eq_of_le_iff_finrank_eq` / `_eq'`

The declarations in this file were extracted from `SKW.Prereqs.IntermediateField` and
submitted upstream as Mathlib PR
[#40300](https://github.com/leanprover-community/mathlib4/pull/40300).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.IntermediateField`) should be deleted, and any
usages redirected to the Mathlib versions.
-/

open Module in
/-- If `F ≤ E` are two intermediate fields of a finite extension `L / K`,
then `F = E` iff [F : K] = [E : K]`. -/
theorem IntermediateField.eq_of_le_iff_finrank_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F E : IntermediateField K L} [FiniteDimensional K L] (h_le : F ≤ E) :
    F = E ↔ finrank K F = finrank K E := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_of_le_of_finrank_eq h_le h⟩
  have := (finrank_mul_finrank K F L).trans (finrank_mul_finrank K E L).symm
  rwa [show finrank F L = finrank E L by rw [h], mul_left_inj' finrank_pos.ne'] at this

open Module in
/-- If `F ≤ E` are two intermediate fields of a finite extension `L / K`,
then `F = E` iff [L : F] = [L : E]`. -/
theorem IntermediateField.eq_of_le_iff_finrank_eq' {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F E : IntermediateField K L} [FiniteDimensional K L] (h_le : F ≤ E) :
    F = E ↔ finrank F L = finrank E L := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_of_le_of_finrank_eq' h_le h⟩
  have := (finrank_mul_finrank K F L).trans (finrank_mul_finrank K E L).symm
  rwa [show finrank K F = finrank K E by rw [h], mul_right_inj' finrank_pos.ne'] at this

end
