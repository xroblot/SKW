module

public import Mathlib.FieldTheory.LinearDisjoint

-- Minimal reproduction of the non-defeq module instance problem.

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable (E F : IntermediateField k L)

-- Case 1: algebra as `instance` — rfl should hold
private noncomputable instance algEsup : Algebra ↥E ↥(E ⊔ F) :=
  (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra

-- Focus: trace the exact synthesis for Module ↥E' ↥(E' ⊔ F')
-- E' and F' are extendScalars of E and F over E ⊓ F

variable [IsGalois k E] [IsGalois k F]

set_option trace.Meta.synthInstance true in
set_option trace.profiler true in
set_option trace.profiler.useHeartbeats true in
set_option trace.profiler.threshold 5000 in
example : True := by
  let _i1 : Algebra ↥(E ⊓ F) ↥E := (IntermediateField.inclusion inf_le_left).toRingHom.toAlgebra
  let E' : IntermediateField ↥(E ⊓ F) L := E.extendScalars (F := E ⊓ F) inf_le_left
  let F' : IntermediateField ↥(E ⊓ F) L := F.extendScalars (F := E ⊓ F) inf_le_right
  let _i2 : Algebra ↥E' ↥(E' ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  -- Trigger Module ↥E' ↥(E' ⊔ F') synthesis
  have := Module.finrank ↥E' ↥(E' ⊔ F')
  trivial
