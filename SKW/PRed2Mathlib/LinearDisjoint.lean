module

public import Mathlib.FieldTheory.LinearDisjoint

set_option linter.style.header false

/-!
# PRed to Mathlib: degrees of the compositum and intersection with a Galois extension

The declarations in this file were extracted from `SKW.Prereqs.Stickelberger` and submitted
upstream as Mathlib PR [#46051](https://github.com/leanprover-community/mathlib4/pull/46051).
There `IntermediateField.finrank_sup_eq_of_inf_eq_bot` is replaced by
`IntermediateField.LinearDisjoint.relfinrank_sup_left`, the main result is
`IntermediateField.relfinrank_sup_eq_relfinrank_inf`, and
`IntermediateField.finrank_sup_mul_finrank_inf_eq` is deduced from it with `A` and `B` explicit
and without finiteness hypotheses.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted, and the usages redirected to the
Mathlib versions.
-/

@[expose] public section

open Module in
lemma IntermediateField.finrank_sup_eq_of_inf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional F K] [FiniteDimensional F L]
    [Algebra K ↑(K ⊔ L)] [IsScalarTower F K ↑(K ⊔ L)] (hinf : K ⊓ L = ⊥) :
    finrank K ↑(K ⊔ L) = finrank F L := by
  rw [← mul_right_inj', ← (LinearDisjoint.of_inf_eq_bot hinf).finrank_sup, finrank_mul_finrank]
  exact finrank_pos.ne'

set_option maxHeartbeats 500000 in
-- The proof goes through several `extendScalars` and `inclusion` algebra structures.
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
open Module in
theorem IntermediateField.finrank_sup_mul_finrank_inf_eq {k L : Type*} [Field k] [Field L] [Algebra
  k L]
    (E F : IntermediateField k L) [FiniteDimensional k E] [FiniteDimensional k F] [IsGalois k E] :
    finrank k ↑(E ⊔ F) * finrank k ↑(E ⊓ F) = finrank k E * finrank k F := by
  let : Algebra E ↑(E ⊔ F) := (inclusion le_sup_left).toRingHom.toAlgebra
  have : FiniteDimensional k ↑(E ⊓ F) := FiniteDimensional.of_injective
    (IntermediateField.inclusion inf_le_left).toLinearMap
    (RingHom.injective _)
  suffices h : finrank E ↑(E ⊔ F) = finrank ↑(E ⊓ F) F by
    rwa [← finrank_mul_finrank k E ↑(E ⊔ F), ← finrank_mul_finrank k ↑(E ⊓ F) F, mul_assoc,
      mul_right_inj' finrank_pos.ne', mul_comm, mul_right_inj' finrank_pos.ne']
  let : Algebra ↑(E ⊓ F) ↑(E ⊔ F) := (inclusion inf_le_sup).toRingHom.toAlgebra
  have : IsScalarTower ↑(E ⊓ F) E ↑(E ⊔ F) := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional ↑(E ⊓ F) E := FiniteDimensional.right k _ _
  have : FiniteDimensional ↑(E ⊓ F) F := FiniteDimensional.right k _ _
  have : finrank ↑(E ⊓ F) E ≠ 0 := finrank_pos.ne'
  rw [← mul_right_inj' this, finrank_mul_finrank]
  let E' : IntermediateField ↑(E ⊓ F) L := E.extendScalars (F := E ⊓ F) inf_le_left
  let F' : IntermediateField ↑(E ⊓ F) L := F.extendScalars (F := E ⊓ F) inf_le_right
  let : Algebra E' ↑(E' ⊔ F') := (inclusion le_sup_left).toRingHom.toAlgebra
  let e' : E ≃ₐ[↑(E ⊓ F)] E' := AlgEquiv.refl
  let f' : F ≃ₐ[↑(E ⊓ F)] F' := AlgEquiv.refl
  let h : ↑(E' ⊔ F') ≃ₗ[↑(E ⊓ F)] ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup) :=
    LinearEquiv.ofEq ↑(E' ⊔ F').toSubalgebra.toSubmodule
      ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup).toSubalgebra.toSubmodule
        (by simpa using (extendScalars_sup (F := E ⊓ F) inf_le_left inf_le_right))
  have : IsGalois ↑(E ⊓ F) E' := by
    have : IsGalois ↑(E ⊓ F) E := IsGalois.tower_top_of_isGalois k _ _
    exact IsGalois.of_algEquiv e'
  have : FiniteDimensional ↑(E ⊓ F) E' := Module.Finite.equiv e'.toLinearEquiv
  have : FiniteDimensional ↑(E ⊓ F) F' := Module.Finite.equiv f'.toLinearEquiv
  calc finrank ↑(E ⊓ F) ↑(E ⊔ F)
      = finrank ↑(E ⊓ F) ↑(E' ⊔ F') := ?_
    _ = finrank ↑(E ⊓ F) E' * finrank E' ↑(E' ⊔ F') := by rw [finrank_mul_finrank]
    _ = finrank ↑(E ⊓ F) E * finrank E' ↑(E' ⊔ F') := by rw [e'.toLinearEquiv.finrank_eq]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F' := by
        rw [← finrank_sup_eq_of_inf_eq_bot E' F']
        ext; simp [E', F', mem_bot]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F := by rw [f'.toLinearEquiv.finrank_eq]
  · rw [LinearEquiv.finrank_eq (M := ↑(E ⊔ F)) (N := ↑(E' ⊔ F'))]
    exact (LinearEquiv.refl ↑(E ⊓ F) ↑(E ⊔ F)).trans h.symm
