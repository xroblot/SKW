module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification

public import SKW.KroneckerWeber.Basic
public import SKW.KroneckerWeber.ClassGroup
public import SKW.KroneckerWeber.Reduction

@[expose] public section

/-!
# Kronecker-Weber for odd prime power cyclic extensions

Every cyclic extension of `ℚ` of odd prime power degree `pᵐ` unramified outside `p` is
contained in `ℚ(ζ_{p^{m+1}})`.

The key step is `prop_kw_exponent_p` from `ClassGroup.lean` (the degree `p` case). The
induction uses `kw_cyclic_compositum`: if the candidate cyclotomic subfield `K'` of degree `pᵐ`
and `K` have non-cyclic compositum, one obtains a `(ℤ/pℤ)²`-extension unramified outside `p`,
contradicting `prop_kw_exponent_p`.
-/

open NumberField Ideal

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime] [Fact (Odd p)]

/-- Every cyclic extension of `ℚ` of odd prime power degree `pᵐ` unramified outside `p` is
cyclotomic (contained in `ℚ(ζ_{p^{m+1}})`). -/
theorem prop_kw_odd_prime_power (m : ℕ) (hm : 0 < m)
    (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)]
    (hK : Module.finrank ℚ K = p ^ m)
    (hKram : UnramifiedOutside K p) :
    Nonempty (K →ₐ[ℚ] CyclotomicField (p ^ (m + 1)) ℚ) := by
  sorry

end

end
