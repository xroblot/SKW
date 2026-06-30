module

public import SKW.KroneckerWeber.OddPrimePower
public import SKW.KroneckerWeber.TwoPower

@[expose] public section

/-!
# The Kronecker-Weber theorem

Every abelian extension of `ℚ` is contained in a cyclotomic field.

## Proof outline

1. Every finite abelian extension is a compositum of cyclic prime power degree extensions
   (`IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top`).
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
subextensions (`IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top`) and recombines the cyclotomic fields, using that
`ℚ⟮ξ m⟯ ≤ ℚ⟮ξ n⟯` whenever `m ∣ n`. -/
lemma kw_reduce_to_prime_power {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A)
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n)
    (K : IntermediateField ℚ A) [NumberField K] [IsAbelianGalois ℚ K]
    (hK : ∀ (L : IntermediateField ℚ A), [NumberField L] → L ≤ K → IsCyclicOfPrimePowDegree L
      → ∃ n : ℕ, 0 < n ∧ L ≤ ℚ⟮ξ n⟯) :
    ∃ n : ℕ, 0 < n ∧ K ≤ ℚ⟮ξ n⟯ := by
  -- TODO: `IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top ℚ ↥K` now decomposes `K` intrinsically, as `C : ι →
  -- IntermediateField ℚ ↥K` with `⨆ i, C i = ⊤`. Bridge each `C i` up to `IntermediateField ℚ A`
  -- via `IntermediateField.lift` , apply `hK` to get `nᵢ` with `C i ≤ ℚ⟮ξ nᵢ⟯`, then take
  -- `n = ∏ fᵢ` and recombine using `ℚ⟮ξ m⟯ ≤ ℚ⟮ξ n⟯` for `m ∣ n` (proof in git, commit ad678c0).
  sorry


/-- **Kronecker-Weber theorem**: every abelian extension of `ℚ` is contained in a cyclotomic
field. -/
theorem kronecker_weber
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ n : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  sorry

end
