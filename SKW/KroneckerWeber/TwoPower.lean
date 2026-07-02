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

open IntermediateField in
/-- The only quadratic extensions of `ℚ` unramified outside `2` are `ℚ(i)`, `ℚ(√-2)`, `ℚ(√2)`.
In particular the maximal real abelian `2`-extension of `ℚ` with exponent `2` unramified outside
`2` is `ℚ(√2)`, which is the subfield of degree `2` of `ℚ(ζ_8)`; so `K ≤ ℚ⟮ξ 8⟯` inside `A`. -/
theorem prop_kw_2_quadratic {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] (hK : Module.finrank ℚ K = 2)
    (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ 8⟯ := by
  sorry

open IntermediateField in
/-- Every cyclic extension of `ℚ` of degree `2ᵐ` unramified outside `2` is cyclotomic:
contained in `ℚ(ζ_{2^{m+2}}) = ℚ⟮ξ (2^(m+2))⟯` inside the ambient field `A`. -/
theorem prop_kw_2_power {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ) (hm : 0 < m)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (hK : Module.finrank ℚ K = 2 ^ m) (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ (2 ^ (m + 2))⟯ := by
  sorry

end

end
