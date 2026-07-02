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

set_option backward.isDefEq.respectTransparency false in
/-- Seam between the ramification reduction and the base cases: a cyclic extension of `ℚ` of
prime-power degree `pᵐ` is contained in a cyclotomic field `ℚ⟮ξ n⟯` (`n > 0`). Combines
`kw_reduce_to_unramified_outside_p` (removing ramification away from `p`, up to a cyclotomic factor)
with `prop_kw_odd_prime_power` / `prop_kw_2_power` (the unramified-outside-`p` base cases). This is
exactly the fact discharging the `hK` hypothesis of `kw_reduce_to_prime_power`. -/
lemma kw_cyclic_primePow_le_cyclotomic {p : ℕ} (hp : p.Prime) {A : Type*} [Field A] [CharZero A]
    {ξ : ℕ → A} (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K]
    [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)] (m : ℕ) (hK : Module.finrank ℚ K = p ^ m) :
    ∃ n, 0 < n ∧ K ≤ ℚ⟮ξ n⟯ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, _, ⟨k, hF₁⟩, hF₂, n₀, hn₀, hKF⟩ :=
    kw_reduce_to_unramified_outside_p ξ hξ K m hK
  obtain ⟨c, hc, hF₃⟩ : ∃ c, 0 < c ∧ F ≤ ℚ⟮ξ c⟯ := by
    obtain rfl | hk := k.eq_zero_or_pos
    · exact ⟨1, one_pos, by simp_all⟩
    · obtain rfl | hodd := eq_or_ne p 2
      · exact ⟨2 ^ (k + 2), by positivity, prop_kw_2_power hξ k hk F hF₁ hF₂⟩
      · have : Fact (Odd p) := ⟨hp.odd_of_ne_two hodd⟩
        exact ⟨p ^ (k + 1), pow_pos (Fact.out : p.Prime).pos _,
          prop_kw_odd_prime_power p hξ k hk F hF₁ hF₂⟩
  refine ⟨c.lcm n₀, Nat.pos_of_ne_zero (Nat.lcm_ne_zero hc.ne' hn₀.ne'), ?_⟩
  have : K ≤ K ⊔ ℚ⟮ξ n₀⟯ := le_sup_left
  refine le_trans this ?_
  have : ℚ⟮ξ (c.lcm n₀)⟯ = ℚ⟮ξ c⟯ ⊔ ℚ⟮ξ n₀⟯ := by
    have : NeZero c := ⟨hc.ne'⟩
    have : NeZero n₀ := ⟨hn₀.ne'⟩
    have : NeZero (c.lcm n₀) := ⟨Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    have : IsCyclotomicExtension {c.lcm n₀} ℚ ℚ⟮ξ (c.lcm n₀)⟯ :=
      (hξ (c.lcm n₀)).adjoinSimple_isCyclotomicExtension _ _ _
    have : IsCyclotomicExtension {c.lcm n₀} ℚ ↑(ℚ⟮ξ c⟯ ⊔ ℚ⟮ξ n₀⟯) := by
      have : IsCyclotomicExtension {c} ℚ ℚ⟮ξ c⟯ := (hξ c).adjoinSimple_isCyclotomicExtension _ _ _
      have : IsCyclotomicExtension {n₀} ℚ ℚ⟮ξ n₀⟯ := (hξ n₀).adjoinSimple_isCyclotomicExtension _ _ _
      exact isCyclotomicExtension_lcm_sup ℚ A _ _ _ _
    exact IntermediateField.isCyclotomicExtension_eq {c.lcm n₀} ℚ _ _ _
  rw [this, hKF]
  exact sup_le_sup_right hF₃ _

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
