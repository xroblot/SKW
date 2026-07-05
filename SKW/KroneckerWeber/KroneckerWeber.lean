module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public import SKW.KroneckerWeber.OddPrimePower
public import SKW.KroneckerWeber.TwoPower
public import SKW.Prereqs.Instances

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
        have : IsAbelianGalois ℚ F := .of_isCyclic ℚ F
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

set_option backward.isDefEq.respectTransparency false in
lemma kw_reduce_to_prime_power_aux {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K]
    [IsAbelianGalois ℚ K] {ι : Type*} (S : Finset ι) (C : ι → IntermediateField ℚ A)
    (hC : ∀ i, ∃ n, 0 < n ∧ C i ≤ ℚ⟮ξ n⟯) (htop : ⨆ i ∈ S, C i = K):
    ∃ n : ℕ, 0 < n ∧ K ≤ ℚ⟮ξ n⟯ := by
  classical
  induction S using Finset.induction generalizing K with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      simp only [Finset.notMem_empty, not_false_eq_true, iSup_neg, iSup_bot] at htop
      simp [← htop]
  | insert i S _ hi =>
      rw [Finset.iSup_insert] at htop
      obtain ⟨n, hn₀, hn₁⟩ := hC i
      let : Algebra ↑(⨆ i ∈ S, C i) K := (inclusion (htop ▸ le_sup_right)).toAlgebra
      have : NumberField ↑(⨆ i ∈ S, C i) := NumberField.of_tower ℚ K _
      have : IsAbelianGalois ℚ ↑(⨆ i ∈ S, C i) :=  IsAbelianGalois.tower_bot ℚ _ K
      obtain ⟨m, hm₀, hm₁⟩ := hi (⨆ i ∈ S, C i) rfl
      have : NeZero n := ⟨hn₀.ne'⟩
      have : NeZero m := ⟨hm₀.ne'⟩
      have : NeZero (n.lcm m) := ⟨(Nat.lcm_pos hn₀ hm₀).ne'⟩
      refine ⟨n.lcm m, NeZero.pos _, (htop ▸ sup_le_sup hn₁ hm₁).trans ?_⟩
      have : IsCyclotomicExtension {n.lcm m} ℚ ↑(ℚ⟮ξ n⟯ ⊔ ℚ⟮ξ m⟯) := by
        have : IsCyclotomicExtension {n} ℚ ℚ⟮ξ n⟯ := (hξ n).adjoinSimple_isCyclotomicExtension n ℚ A
        have : IsCyclotomicExtension {m} ℚ ℚ⟮ξ m⟯ := (hξ m).adjoinSimple_isCyclotomicExtension m ℚ A
        exact isCyclotomicExtension_lcm_sup _ _ _ _ _ _
      have : IsCyclotomicExtension {n.lcm m} ℚ ℚ⟮ξ (n.lcm m)⟯ :=
        (hξ (n.lcm m)).adjoinSimple_isCyclotomicExtension (n.lcm m) ℚ A
      exact isCyclotomicExtension_le_of_dvd _ _ (n.lcm m) (n.lcm m) _ _ dvd_rfl

set_option backward.isDefEq.respectTransparency false in
/-- Reduction of Kronecker-Weber to the cyclic prime power case (in `IntermediateField ℚ A`
currency): if every cyclic subextension of `K` of prime power degree lies in a cyclotomic field
`ℚ⟮ξ n⟯` (with `n > 0`), then so does `K`. The proof decomposes `K` as a compositum of such
subextensions (`IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top`) and recombines the cyclotomic fields, using that
`ℚ⟮ξ m⟯ ≤ ℚ⟮ξ n⟯` whenever `m ∣ n`. -/
lemma kw_reduce_to_prime_power {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K]
    [IsAbelianGalois ℚ K] :
    ∃ n : ℕ, 0 < n ∧ K ≤ ℚ⟮ξ n⟯ := by
  obtain ⟨ι, _, C, hC, htop⟩ := IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top ℚ K
  apply kw_reduce_to_prime_power_aux hξ _ Finset.univ (fun i ↦ lift (C i)) ?_ ?_
  · intro i
    obtain ⟨_, _, ⟨p, k, hp, _, hrC⟩⟩ := hC i
    rw [← Nat.prime_iff] at hp
    exact kw_cyclic_primePow_le_cyclotomic hp hξ _ k (by rwa [finrank_lift, eq_comm])
  · have := (lift_inj _ _).mpr htop
    rwa [← iSup_univ, ← Finset.coe_univ, Finset.iSup_coe, lift_iSup _ _ _ Finset.univ,
      lift_top] at this

/-- **Kronecker-Weber theorem**: every abelian extension of `ℚ` is contained in a cyclotomic
field. -/
theorem kronecker_weber
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ n : ℕ, Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by
  let A := AlgClo
  have {n : ℕ} : HasEnoughRootsOfUnity ℂ n := by exact?
  have := kw_reduce_to_prime_power (A := ℂ)
  sorry

end
