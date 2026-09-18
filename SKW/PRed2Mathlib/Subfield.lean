module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

/-!
# PRed to Mathlib: the `map`/`comap` Galois coinsertion for subfields, and totally real suprema

The declarations in this file were extracted from `SKW.Prereqs.Subfield` and submitted upstream as
Mathlib PR [#43924](https://github.com/leanprover-community/mathlib4/pull/43924), which also
generalizes `NumberField.isTotallyReal_sup` and `NumberField.isTotallyReal_iSup` by dropping the
assumption that the ambient field is algebraic over `ℚ`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
(and its import in `SKW.Prereqs.Subfield`) should be deleted, and any usages redirected to the
Mathlib versions.
-/

namespace Subfield

variable {K : Type*} [Field K]

section GaloisCoinsertion

variable {L : Type*} [Field L] {ι : Sort*} (f : K →+* L)

/-- `map f` and `comap f` form a `GaloisCoinsertion`: a ring homomorphism out of a field is
injective. -/
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap]

/-- Same statement as `Subfield.comap_map`, proved through `Subfield.gciMapComap`; it is meant to
replace it when this material goes to Mathlib. -/
theorem comap_map' (S : Subfield K) : (S.map f).comap f = S :=
  (gciMapComap f).u_l_eq _

theorem comap_surjective : Function.Surjective (comap f) :=
  (gciMapComap f).u_surjective

theorem map_injective : Function.Injective (map f) :=
  (gciMapComap f).l_injective

theorem comap_inf_map (S T : Subfield K) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap f).u_inf_l _ _

theorem comap_iInf_map (S : ι → Subfield K) : (⨅ i, (S i).map f).comap f = ⨅ i, S i :=
  (gciMapComap f).u_iInf_l _

theorem comap_sup_map (S T : Subfield K) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap f).u_sup_l _ _

theorem comap_iSup_map (S : ι → Subfield K) : (⨆ i, (S i).map f).comap f = ⨆ i, S i :=
  (gciMapComap f).u_iSup_l _

theorem map_le_map_iff {S T : Subfield K} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap f).l_le_l_iff

/-- `comap` commutes with `⊔` for subfields lying in the range of `f`. -/
theorem comap_sup {S T : Subfield L} (hS : S ≤ f.fieldRange) (hT : T ≤ f.fieldRange) :
    (S ⊔ T).comap f = S.comap f ⊔ T.comap f := by
  rw [← map_comap_eq_self hS, ← map_comap_eq_self hT, comap_sup_map, comap_map', comap_map']

/-- `comap` commutes with `⨆` for subfields lying in the range of `f`. -/
theorem comap_iSup {S : ι → Subfield L} (hS : ∀ i, S i ≤ f.fieldRange) :
    (⨆ i, S i).comap f = ⨆ i, (S i).comap f := by
  have : ∀ i, ((S i).comap f).map f = S i := fun i ↦ map_comap_eq_self (hS i)
  calc (⨆ i, S i).comap f = (⨆ i, ((S i).comap f).map f).comap f := by simp_rw [this]
    _ = ⨆ i, (S i).comap f := comap_iSup_map f _

section Subtype

variable {s t : Subfield K}

@[simp]
theorem comap_subtype_eq_top : t.comap s.subtype = ⊤ ↔ s ≤ t := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ eq_top_iff.mpr fun z _ ↦ mem_comap.mpr (h z.2)⟩
  exact mem_comap.mp (h ▸ mem_top (⟨x, hx⟩ : s))

@[simp]
theorem comap_subtype_self (s : Subfield K) : s.comap s.subtype = ⊤ :=
  comap_subtype_eq_top.mpr le_rfl

theorem map_comap_subtype : (t.comap s.subtype).map s.subtype = s ⊓ t :=
  SetLike.coe_injective <| by
    ext x
    exact ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨⟨x, h₁⟩, h₂, rfl⟩⟩

end Subtype

end GaloisCoinsertion

end Subfield

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
