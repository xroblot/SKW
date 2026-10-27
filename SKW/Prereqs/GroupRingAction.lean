module

public import Mathlib.Algebra.MonoidAlgebra.Basic

set_option linter.style.header false

/-!
# Action of a group ring on a commutative monoid

If a monoid `G` acts on a commutative monoid `M` by monoid homomorphisms, then `ℕ[G]` acts on `M`
by `m ^ ∑ nᵍ g = ∏ (g • m) ^ nᵍ`.
-/

public section

namespace MonoidAlgebra

variable {G M : Type*} [Monoid G]

section CommMonoid

variable [CommMonoid M] [MulDistribMulAction G M]

/-- The action of `ℕ[G]` on a commutative monoid `M` on which `G` acts by monoid homomorphisms:
`m ^ ∑ nᵍ g = ∏ (g • m) ^ nᵍ`. -/
instance : Pow M (MonoidAlgebra ℕ G) where
  pow m θ := θ.coeff.prod fun g n ↦ (g • m) ^ n

theorem pow_def (m : M) (θ : MonoidAlgebra ℕ G) :
    m ^ θ = θ.coeff.prod fun g n ↦ (g • m) ^ n := rfl

@[simp]
theorem pow_zero (m : M) : m ^ (0 : MonoidAlgebra ℕ G) = 1 := by
  simp [pow_def]

@[simp]
theorem pow_single (m : M) (g : G) (n : ℕ) : m ^ single g n = (g • m) ^ n := by
  simp [pow_def]

theorem pow_add (m : M) (θ θ' : MonoidAlgebra ℕ G) : m ^ (θ + θ') = m ^ θ * m ^ θ' := by
  simp_rw [pow_def, coeff_add]
  exact Finsupp.prod_add_index' (fun _ ↦ _root_.pow_zero _) fun _ ↦ _root_.pow_add _

theorem pow_sum {ι : Type*} (m : M) (s : Finset ι) (θ : ι → MonoidAlgebra ℕ G) :
    m ^ (∑ i ∈ s, θ i) = ∏ i ∈ s, m ^ θ i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, pow_add, ih]

theorem pow_nsmul (m : M) (n : ℕ) (θ : MonoidAlgebra ℕ G) : m ^ (n • θ) = (m ^ θ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, pow_add, ih, pow_succ]

@[simp]
theorem pow_one (m : M) : m ^ (1 : MonoidAlgebra ℕ G) = m := by
  simp [one_def]

@[simp]
theorem one_pow (θ : MonoidAlgebra ℕ G) : (1 : M) ^ θ = 1 := by
  simp [pow_def]

theorem mul_pow (m m' : M) (θ : MonoidAlgebra ℕ G) : (m * m') ^ θ = m ^ θ * m' ^ θ := by
  simp [pow_def, _root_.mul_pow, Finsupp.prod_mul]

theorem smul_pow (g : G) (m : M) (θ : MonoidAlgebra ℕ G) : g • m ^ θ = m ^ (single g 1 * θ) := by
  induction θ using induction_linear with
  | zero => simp
  | add θ θ' h h' => rw [pow_add, smul_mul', h, h', mul_add, pow_add]
  | single h n => simp [single_mul_single, mul_smul]

/-- Multiplication in `ℕ[G]` acts in the reversed order, since `G` acts on the left. -/
theorem pow_mul (m : M) (θ θ' : MonoidAlgebra ℕ G) : m ^ (θ * θ') = (m ^ θ') ^ θ := by
  induction θ using induction_linear with
  | zero => simp
  | add θ₁ θ₂ h₁ h₂ => rw [add_mul, pow_add, pow_add, h₁, h₂]
  | single g n =>
    rw [show single g n = n • single g 1 by rw [smul_single, smul_eq_mul, mul_one],
      smul_mul_assoc, pow_nsmul, pow_nsmul, ← smul_pow, pow_single, _root_.pow_one]

end CommMonoid

end MonoidAlgebra
