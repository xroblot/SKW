module

public import SKW.KroneckerWeber.OddPrimePower
public import SKW.KroneckerWeber.TwoPower

@[expose] public section

/-!
# The Kronecker-Weber theorem

Every abelian extension of `ℚ` is contained in a cyclotomic field.

## Proof outline

1. Every finite abelian extension is a compositum of cyclic prime power degree extensions
   (`kw_abelian_cyclic_decomp`).
2. Each cyclic prime power degree extension can be replaced, up to a cyclotomic factor, by one
   unramified outside `p` (`kw_reduce_to_unramified_outside_p` / `kw_ramification_reduction`).
3. Cyclic prime power degree extensions unramified outside `p` are cyclotomic:
   - Odd prime `p`: `prop_kw_odd_prime_power`.
   - `p = 2`: `prop_kw_2_power`.
4. A compositum of cyclotomic fields is cyclotomic.
-/

open NumberField IntermediateField

def IsCyclicOfPrimeOrder (K : Type*) [Field K] [NumberField K] : Prop :=
  IsAbelianGalois ℚ K ∧ ∃ p k : ℕ, p.Prime ∧ Nat.card Gal(K/ℚ) = p ^ k

example {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A) (hξ : ∀ n, IsPrimitiveRoot (ξ n) n)
    (K : IntermediateField ℚ A) [NumberField K] [IsAbelianGalois ℚ K]
    (hK : ∀ (L : IntermediateField ℚ A), [NumberField L] → (hL : L ≤ K) → IsCyclicOfPrimeOrder L
      → ∃ (n : ℕ), L ≤ ℚ⟮ξ n⟯) :
    ∃ (n : ℕ), K ≤ ℚ⟮ξ n⟯ := by
  let : CommGroup Gal(K/ℚ) := IsMulCommutative.instCommGroup
  obtain ⟨ι, j, _, _, fp, hp, fk, ⟨e⟩⟩ := CommGroup.equiv_free_prod_prod_multiplicative_zmod Gal(K/ℚ)
  refine ⟨∏ i : ι, fp i ^ fk i, ?_⟩
  

  sorry

/-- **Kronecker-Weber theorem**: every abelian extension of `ℚ` is contained in a cyclotomic
field. -/
theorem kronecker_weber
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ n : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  sorry

end
