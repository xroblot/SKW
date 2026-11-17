module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option linter.style.header false

@[expose] public section

/-!
# PRed to Mathlib: totally real suprema

The declarations in this file were extracted from `SKW.Prereqs.Subfield` and submitted upstream as
Mathlib PR [#43924](https://github.com/leanprover-community/mathlib4/pull/43924), which
generalizes `NumberField.isTotallyReal_sup` and `NumberField.isTotallyReal_iSup` by dropping the
assumption that the ambient field is algebraic over `ℚ`. The `map`/`comap` Galois coinsertion for
subfields, split off as #43925, is now in Mathlib.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
(and its import in `SKW.Prereqs.KroneckerWeber`) should be deleted, and any usages redirected to
the Mathlib versions.
-/

open Subfield NumberField in
/-- The compositum of totally real subfields is totally real. -/
instance NumberField.isTotallyReal_iSup' {A : Type*} [Field A] {ι : Type*} (F : ι → Subfield A)
    [hF : ∀ i, NumberField.IsTotallyReal (F i)] :
    NumberField.IsTotallyReal ↑(⨆ i, F i) := by
  refine ⟨fun w ↦ InfinitePlace.isReal_iff.mpr <|
      ComplexEmbedding.isReal_iff.mpr <| RingHom.ext fun z ↦ RingHom.mem_eqLocusField.mp ?_⟩
  have : (ComplexEmbedding.conjugate w.embedding).eqLocusField w.embedding = ⊤ := by
    rw [eq_top_iff, ← comap_subtype_self, comap_iSup _ (fun _ ↦ by simpa using le_iSup _ _),
      iSup_le_iff]
    refine fun _ x hx ↦ RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal
        (w.embedding.comp (Subfield.inclusion ?_))) ⟨x, hx⟩
    exact le_iSup _ _
  exact this ▸ Subsemiring.mem_top z

open NumberField in
/-- The compositum of two totally real subfields is totally real. -/
instance NumberField.isTotallyReal_sup' {A : Type*} [Field A] {E F : Subfield A}
    [NumberField.IsTotallyReal E] [NumberField.IsTotallyReal F] :
    NumberField.IsTotallyReal ↑(E ⊔ F) := by
  rw [sup_eq_iSup]
  exact isTotallyReal_iSup' (fun b ↦ cond b E F) (hF := by rintro (_ | _) <;> assumption)


end
