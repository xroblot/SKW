module

public import Mathlib.NumberTheory.NumberField.CMField

open NumberField IsCMField

variable (K : Type*) [Field K] [CharZero K] [IsCMField K] [NumberField K]

example (u : (𝓞 K)ˣ) :
    ∃ ζ : Units.torsion K, ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧ u ^ indexRealUnits K  = ζ * v := by
  

  -- refine ⟨unitsMulComplexConjInv K u, u * (unitsMulComplexConjInv K u)⁻¹, ?_,
  --   by simp [unitsMulComplexConjInv_apply]⟩
  -- rw [← unitsMulComplexConjInv_ker, MonoidHom.mem_ker]
  -- rw [map_mul, InvMemClass.coe_inv, unitsMulComplexConjInv_apply]
