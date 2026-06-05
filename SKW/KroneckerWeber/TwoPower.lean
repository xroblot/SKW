module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic

public import SKW.KroneckerWeber.Basic
public import SKW.KroneckerWeber.Reduction

@[expose] public section

/-!
# Kronecker-Weber for 2-power cyclic extensions

This file handles the `p = 2` case of the reduction to prime power degree:

- `prop_kw_2_quadratic`: The only quadratic extensions of `ℚ` unramified outside `2` are
  `ℚ(i)`, `ℚ(√-2)`, `ℚ(√2)`. In particular the maximal real one is `ℚ(√2) ⊂ ℚ(ζ_8)`.
- `prop_kw_2_power`: Every cyclic extension of `ℚ` of degree `2ᵐ` unramified outside `2` is
  cyclotomic.

The proof of `prop_kw_2_power` uses `prop_kw_exponent_p` (the odd prime analogue adapted to
`p = 2`) and `kw_cyclic_compositum` to compare `K` with the appropriate subfield of
`ℚ(ζ_{2^{m+2}})`.
-/

open NumberField Ideal

noncomputable section

/-- The only quadratic extensions of `ℚ` unramified outside `2` are `ℚ(i)`, `ℚ(√-2)`, `ℚ(√2)`.
In particular the maximal real abelian `2`-extension of `ℚ` with exponent `2` unramified outside
`2` is `ℚ(√2)`, which is the subfield of degree `2` of `ℚ(ζ_8)`. -/
theorem prop_kw_2_quadratic
    (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (hK : Module.finrank ℚ K = 2)
    (hKram : UnramifiedOutside K 2) :
    Nonempty (K →ₐ[ℚ] CyclotomicField 8 ℚ) := by
  sorry

/-- Every cyclic extension of `ℚ` of degree `2ᵐ` unramified outside `2` is cyclotomic
(contained in `ℚ(ζ_{2^{m+2}})`). -/
theorem prop_kw_2_power (m : ℕ) (hm : 0 < m)
    (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
    (hK : Module.finrank ℚ K = 2 ^ m)
    (hKram : UnramifiedOutside K 2) :
    Nonempty (K →ₐ[ℚ] CyclotomicField (2 ^ (m + 2)) ℚ) := by
  sorry

end

end
