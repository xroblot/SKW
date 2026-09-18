module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

/-!
# Suprema of subfields

Induction principles for suprema of subfields, a Galois coinsertion for `map`/`comap`, and the
fact that a supremum of totally real subfields is totally real.

`Subfield.iSup_induction`, its dependent version `Subfield.iSup_induction'` and the binary
`Subfield.sup_induction`, following `Subalgebra.iSup_induction` and `Submonoid.iSup_induction`.
Candidates for Mathlib: the `Subfield` API has `closure_induction` but no induction principle for
suprema.
-/

namespace Subfield

variable {K : Type*} [Field K]

/-- An induction principle for elements of `⨆ i, S i`. If `motive` holds for `1` and for every
element of each `S i`, and is preserved by addition, negation, inversion and multiplication, then
it holds for every element of the supremum. -/
@[elab_as_elim]
theorem iSup_induction {ι : Sort*} (S : ι → Subfield K) {motive : K → Prop} {x : K}
    (mem : x ∈ ⨆ i, S i) (basic : ∀ i, ∀ y ∈ S i, motive y) (one : motive 1)
    (add : ∀ y z, motive y → motive z → motive (y + z))
    (neg : ∀ y, motive y → motive (-y)) (inv : ∀ y, motive y → motive y⁻¹)
    (mul : ∀ y z, motive y → motive z → motive (y * z)) :
    motive x := by
  let T : Subfield K :=
    { carrier := {x | motive x}
      mul_mem' := mul _ _
      one_mem' := one
      add_mem' := add _ _
      zero_mem' := by simpa using add 1 (-1) one (neg 1 one)
      neg_mem' := neg _
      inv_mem' := inv }
  suffices (⨆ i, S i) ≤ T from this mem
  exact iSup_le fun i y hy ↦ basic i y hy

/-- A dependent version of `Subfield.iSup_induction`. -/
@[elab_as_elim]
theorem iSup_induction' {ι : Sort*} (S : ι → Subfield K) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    {x : K} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ (i) (y) (hy : y ∈ S i), motive y (le_iSup S i hy))
    (one : motive 1 (one_mem _))
    (add : ∀ y z hy hz, motive y hy → motive z hz → motive (y + z) (add_mem ‹_› ‹_›))
    (neg : ∀ y hy, motive y hy → motive (-y) (neg_mem ‹_›))
    (inv : ∀ y hy, motive y hy → motive y⁻¹ (inv_mem ‹_›))
    (mul : ∀ y z hy hz, motive y hy → motive z hz → motive (y * z) (mul_mem ‹_› ‹_›)) :
    motive x mem := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, S i) (hc : motive x hx) ↦ hc
  exact iSup_induction S (motive := fun y ↦ ∃ h, motive y h) mem
    (fun _ _ h ↦ ⟨_, basic _ _ h⟩) ⟨_, one⟩
    (fun _ _ h h' ↦ ⟨_, add _ _ _ _ h.choose_spec h'.choose_spec⟩)
    (fun _ h ↦ ⟨_, neg _ _ h.choose_spec⟩) (fun _ h ↦ ⟨_, inv _ _ h.choose_spec⟩)
    (fun _ _ h h' ↦ ⟨_, mul _ _ _ _ h.choose_spec h'.choose_spec⟩)

/-- An induction principle for elements of `E ⊔ F`. -/
@[elab_as_elim]
theorem sup_induction {E F : Subfield K} {motive : K → Prop} {x : K} (mem : x ∈ E ⊔ F)
    (memE : ∀ y ∈ E, motive y) (memF : ∀ y ∈ F, motive y) (one : motive 1)
    (add : ∀ y z, motive y → motive z → motive (y + z))
    (neg : ∀ y, motive y → motive (-y)) (inv : ∀ y, motive y → motive y⁻¹)
    (mul : ∀ y z, motive y → motive z → motive (y * z)) :
    motive x := by
  let T : Subfield K :=
    { carrier := {x | motive x}
      mul_mem' := mul _ _
      one_mem' := one
      add_mem' := add _ _
      zero_mem' := by simpa using add 1 (-1) one (neg 1 one)
      neg_mem' := neg _
      inv_mem' := inv }
  suffices E ⊔ F ≤ T from this mem
  exact sup_le memE memF

/-- A dependent version of `Subfield.sup_induction`. -/
@[elab_as_elim]
theorem sup_induction' {E F : Subfield K} {motive : ∀ x, x ∈ E ⊔ F → Prop} {x : K}
    (mem : x ∈ E ⊔ F)
    (memE : ∀ (y) (hy : y ∈ E), motive y ((le_sup_left : E ≤ E ⊔ F) hy))
    (memF : ∀ (y) (hy : y ∈ F), motive y ((le_sup_right : F ≤ E ⊔ F) hy))
    (one : motive 1 (one_mem _))
    (add : ∀ y z hy hz, motive y hy → motive z hz → motive (y + z) (add_mem ‹_› ‹_›))
    (neg : ∀ y hy, motive y hy → motive (-y) (neg_mem ‹_›))
    (inv : ∀ y hy, motive y hy → motive y⁻¹ (inv_mem ‹_›))
    (mul : ∀ y z hy hz, motive y hy → motive z hz → motive (y * z) (mul_mem ‹_› ‹_›)) :
    motive x mem := by
  refine Exists.elim ?_ fun (hx : x ∈ E ⊔ F) (hc : motive x hx) ↦ hc
  exact sup_induction (motive := fun y ↦ ∃ h, motive y h) mem
    (fun _ h ↦ ⟨_, memE _ h⟩) (fun _ h ↦ ⟨_, memF _ h⟩) ⟨_, one⟩
    (fun _ _ h h' ↦ ⟨_, add _ _ _ _ h.choose_spec h'.choose_spec⟩)
    (fun _ h ↦ ⟨_, neg _ _ h.choose_spec⟩) (fun _ h ↦ ⟨_, inv _ _ h.choose_spec⟩)
    (fun _ _ h h' ↦ ⟨_, mul _ _ _ _ h.choose_spec h'.choose_spec⟩)

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
