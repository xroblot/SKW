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

/-- Reduction of Kronecker-Weber to the cyclic prime power case (in `IntermediateField ℚ A`
currency): if every cyclic subextension of `K` of prime power degree lies in a cyclotomic field
`ℚ⟮ξ n⟯` (with `n > 0`), then so does `K`. The proof decomposes `K` as a compositum of such
subextensions (`kw_abelian_cyclic_decomp`) and recombines the cyclotomic fields, using that
`ℚ⟮ξ m⟯ ≤ ℚ⟮ξ n⟯` whenever `m ∣ n`. -/
lemma kw_reduce_to_prime_power {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A)
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n)
    (K : IntermediateField ℚ A) [NumberField K] [IsAbelianGalois ℚ K]
    (hK : ∀ (L : IntermediateField ℚ A), [NumberField L] → L ≤ K → IsCyclicOfPrimePowerDegree L
      → ∃ n : ℕ, 0 < n ∧ L ≤ ℚ⟮ξ n⟯) :
    ∃ n : ℕ, 0 < n ∧ K ≤ ℚ⟮ξ n⟯ := by
  obtain ⟨ι, _, C, hC, hsup⟩ := kw_abelian_cyclic_decomp K
  have mono : ∀ {m n : ℕ}, n ≠ 0 → m ∣ n → (ℚ⟮ξ m⟯ : IntermediateField ℚ A) ≤ ℚ⟮ξ n⟯ := by
    intro m n hn hmn
    haveI : NeZero n := ⟨hn⟩
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have hpow : ξ m ^ n = 1 := by
      obtain ⟨k, rfl⟩ := hmn
      rw [pow_mul, (hξ m).pow_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := (hξ n).eq_pow_of_pow_eq_one hpow
    rw [← hk]
    exact pow_mem (IntermediateField.subset_adjoin ℚ {ξ n} rfl) k
  have key : ∀ i, ∃ n : ℕ, 0 < n ∧ C i ≤ ℚ⟮ξ n⟯ := by
    intro i
    haveI : FiniteDimensional ℚ (C i) :=
      .of_injective (IntermediateField.inclusion (hC i).1).toLinearMap
        (IntermediateField.inclusion_injective (hC i).1)
    haveI : NumberField (C i) := ⟨⟩
    exact hK (C i) (hC i).1 (hC i).2
  choose f hf0 hf using key
  refine ⟨∏ i, f i, Finset.prod_pos fun i _ => hf0 i, ?_⟩
  rw [← hsup, iSup_le_iff]
  exact fun i => (hf i).trans
    (mono (Finset.prod_pos fun j _ => hf0 j).ne' (Finset.dvd_prod_of_mem f (Finset.mem_univ i)))


/-- **Kronecker-Weber theorem**: every abelian extension of `ℚ` is contained in a cyclotomic
field. -/
theorem kronecker_weber
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ n : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  sorry

end
