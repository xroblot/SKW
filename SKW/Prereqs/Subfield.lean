module

public import Mathlib.Algebra.Field.Subfield.Basic
public import SKW.PRed2Mathlib.Subfield

@[expose] public section

/-!
# Induction principles for suprema of subfields

`Subfield.iSup_induction`, its dependent version `Subfield.iSup_induction'`, the binary
`Subfield.sup_induction` and `Subfield.sup_induction'`, following `Subalgebra.iSup_induction` and
`Submonoid.iSup_induction`. Candidates for Mathlib: the `Subfield` API has `closure_induction` but
no induction principle for suprema.
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

end Subfield

end
