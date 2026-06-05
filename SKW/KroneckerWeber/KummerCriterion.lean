module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

/-!
# Criterion for a Kummer extension to be abelian

Let `F` be a field containing `μ_p`, `μ ∈ F×`, `L = F(ᵖ√μ)`. A subgroup `G₀ ≤ Gal(F/ℚ)` lifts
to `Gal(L/ℚ)` (i.e. `L/ℚ` is Galois over `G₀`) if and only if for every `σ ∈ G₀` there exists
`ξ ∈ F×` such that `σ(μ) = ξᵖ · μ^{a(σ)}` for some `a(σ) ∈ ℤ`.

In particular, `L/ℚ` is abelian iff for every `σ_a ∈ Gal(F/ℚ)` there exists `ξ ∈ F×` with
`σ_a(μ) = ξᵖ · μ^a`.
-/

open Polynomial IntermediateField

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime]
variable {F : Type*} [Field F] [Algebra K F]
variable {μ : F} {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]

/-- A Kummer extension `L = F(ᵖ√μ)` is Galois over `K` if for every `σ ∈ Gal(F/K)` there exists
`ξ ∈ F×` and `a : ℤ` such that `σ(μ) = ξᵖ · μ^a`. This is the key criterion making the Kummer
extension abelian over a base field. -/
lemma kummer_abelian_criterion
    (hμ : μ ≠ 0)
    (hF : (primitiveRoots p F).Nonempty)
    (hL : IsSplittingField F L (X ^ p - C μ)) :
    (∀ σ : F ≃ₐ[K] F, ∃ (ξ : F) (a : ℤ), σ μ = ξ ^ p * μ ^ a) ↔
    IsGalois K L := by
  sorry

end
