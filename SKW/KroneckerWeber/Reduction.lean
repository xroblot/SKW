module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.Algebra.IsPrimePow

public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.CyclotomicField

@[expose] public section

/-!
# Reduction steps for Kronecker-Weber

This file establishes the reduction steps that allow us to prove Kronecker-Weber by induction:

1. `kw_cyclic_compositum`: If two cyclic `p`-extensions have cyclic compositum, one contains the
   other.
2. `kw_minkowski`: Every non-trivial extension of `ℚ` is ramified at some finite prime.
3. `kw_ramification_reduction`: Given `K/ℚ` cyclic of prime power degree with `q ≠ p` ramified,
   there exists a cyclotomic `L/ℚ` such that `KL = FL` for `F/ℚ` cyclic of prime power degree
   with `q` unramified.

The decomposition of a finite abelian extension into cyclic prime power subextensions is
`IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top` (in `SKW/Prereqs/IntermediateFields.lean`).
The reduction of the general (abelian) case to the cyclic prime power case
(`kw_reduce_to_prime_power`) lives in `KroneckerWeber.lean`, in `IntermediateField ℚ A` currency.
-/

open NumberField Ideal Pointwise Module IntermediateField

noncomputable section

/-- `K/ℚ` is a cyclic Galois extension of prime power degree (`> 1`). -/
def IsCyclicOfPrimePowDegree (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  IsGalois ℚ K ∧ IsCyclic Gal(K/ℚ) ∧ IsPrimePow (Module.finrank ℚ K)

variable {p : ℕ} [hp : Fact p.Prime]

/-- Two cyclic `p`-extensions of `ℚ` whose compositum is cyclic must be comparable. -/
lemma kw_cyclic_compositum (L : Type*) [Field L] [NumberField L] (K K' : IntermediateField ℚ L)
    (h : finrank ℚ K ∣ finrank ℚ K') [IsGalois ℚ L] [hCL : IsCyclic Gal(L/ℚ)] :
    K ≤ K' := by
  rw [← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/ℚ) ℚ L K,
    ← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/ℚ) ℚ L K']
  apply IsGaloisGroup.fixedPoints_le_of_le
  rw [IsCyclic.subgroup_le_subgroup_iff, IsGaloisGroup.card_fixingSubgroup_eq_finrank,
    IsGaloisGroup.card_fixingSubgroup_eq_finrank]
  have hd : finrank ℚ K ∣ finrank ℚ L := finrank_mul_finrank ℚ K L ▸ dvd_mul_right _ _
  have hd' : finrank ℚ K' ∣ finrank ℚ L := finrank_mul_finrank ℚ K' L ▸ dvd_mul_right _ _
  have he : finrank K L = finrank ℚ L / finrank ℚ K :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  have he' : finrank K' L = finrank ℚ L / finrank ℚ K' :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  rwa [he, he', Nat.div_dvd_div_iff finrank_pos finrank_pos hd' hd]

/-- Every non-trivial extension of `ℚ` is ramified at some finite prime (Minkowski). -/
lemma kw_minkowski (K : Type*) [Field K] [NumberField K] (h : Module.finrank ℚ K > 1) :
    ∃ q : ℕ, q.Prime ∧ ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal ∧ 𝔮.LiesOver (Ideal.span {(q : ℤ)}) ∧
      1 < Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 := by
  obtain ⟨𝔮, hq, hq'⟩ := exists_not_isUnramifiedAt_int (K := K) (𝒪 := 𝓞 K) h.ne'
  refine ⟨absNorm (Ideal.under ℤ 𝔮), Nat.absNorm_under_prime 𝔮, 𝔮, hq, Int.liesOver_span_absNorm 𝔮, ?_⟩
  rwa [Int.ideal_span_absNorm_eq_self, ← Algebra.not_isUnramifiedAt_iff_of_isDedekindDomain]
  exact IsMaximal.ne_bot_of_isIntegral_int 𝔮

/-- Ramification reduction: given `K/ℚ` cyclic of prime power degree `pᵐ` with `q ≠ p` ramified,
there is a cyclic `F/ℚ` of degree `pᵐ` (in the same ambient field `A`), unramified at `q` and not
ramified at any prime where `K` is unramified, such that `K · ℚ(ζ_q) = F · ℚ(ζ_q)`. This removes `q`
from the set of ramified primes at the cost of the `q`-th cyclotomic factor. (`ℚ(ζ_q)` already
suffices, since for the abelian `K` the tame inertia order at `q` divides `q - 1`.) -/
lemma kw_ramification_reduction {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] (m : ℕ) (hm : 0 < m) (hK : Module.finrank ℚ K = p ^ m) (q : ℕ)
    (hq : q.Prime) (hqp : q ≠ p) (hram : ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F),
      IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ Module.finrank ℚ F = p ^ m ∧
      Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)}) ∧
      (∀ q' : ℕ, q'.Prime → Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q' : ℤ)}) →
        Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q' : ℤ)})) ∧
      K ⊔ ℚ⟮ξ q⟯ = F ⊔ ℚ⟮ξ q⟯ := by

  -- Take `Λ = ℚ(ζ_q) = ℚ⟮ξ q⟯`, i.e. `r = 1`: the tame inertia at `q` has order dividing `q - 1`.
  --
  -- Step 1 (tame inertia). Let `𝔮` be a prime of `𝓞 K` over `q`. Since `q ≠ p` and `[K:ℚ] = pᵐ`,
  --   the inertia group `I = I(𝔮 ∣ q) ⊆ Gal(K/ℚ)` is cyclic (`TameRamification.isCyclic_inertia`),
  --   of order `p^a` with `a ≥ 1` (ramified, from `hram`), and tame (`q ≠ p`).
  -- Step 2 (degree divides `q - 1`). `card_inertia_dvd_card_sub_one` (specialized to `R = ℤ`,
  --   `S = 𝓞 K`, `G = Gal(K/ℚ)`, so `N𝔭 = q`) gives `|I| = p^a ∣ q - 1 = [ℚ(ζ_q) : ℚ]`.
  -- Step 3 (matching cyclotomic subfield). `Gal(ℚ(ζ_q)/ℚ) ≃ (ℤ/q)ˣ` is cyclic of order `q - 1`,
  --   hence `ℚ(ζ_q)` has a unique subfield `M` of degree `p^a`, cyclic and totally ramified at `q`,
  --   whose inertia carries the same tame character as `I`.
  -- Step 4 (Abhyankar / diagonal inertia). In `L := K ⊔ ℚ⟮ξ q⟯`, the tame inertia at `q` is cyclic
  --   and embeds (via the tame character) into the inertia of `K` and of `M`. Let `F` be the fixed
  --   field of the diagonal inertia. Then:
  --     • `F` is unramified at `q` (the diagonal inertia is cancelled);
  --     • `F` is cyclic of degree `pᵐ` (`F ≃ K` through the projection mod inertia);
  --     • `K ⊔ ℚ⟮ξ q⟯ = F ⊔ ℚ⟮ξ q⟯`;
  --     • `F` introduces no new ramified prime (`F ⊆ L`, and `L` ramifies only where `K` or
  --       `ℚ(ζ_q)` do, i.e. at `q` and the primes ramified in `K`).
  -- Conclude with `⟨F, inferInstance, …⟩`.
  --
  -- Missing infrastructure (to build first):
  --   (a) specialization of `TameRamification` to `Gal(K/ℚ) ↷ 𝓞 K / ℤ` (the action instances +
  --       `card_inertia_dvd_card_sub_one` giving `p^a ∣ q - 1`);
  --   (b) the cyclic subfield of `ℚ(ζ_q)` of degree `d ∣ q - 1` and its total ramification at `q`;
  --   (c) the tame "Abhyankar" compositum lemma producing `F` with `K ⊔ Λ = F ⊔ Λ`.
  sorry

/-- Auxiliary form of `kw_reduce_to_unramified_outside_p`, generalized over a finite set `S` of
primes (assumed to contain every `q ≠ p` ramified in `K`) and over `K`. Proved by induction on `S`,
peeling one ramified prime at a time with `kw_ramification_reduction`. -/
lemma kw_reduce_to_unramified_outside_p_aux {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A)
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ) (hm : 0 < m) (S : Finset ℕ)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (hK : Module.finrank ℚ K = p ^ m)
    (hram : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ S → Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})) :
      ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (_ : IsGalois ℚ F) (_ : IsCyclic Gal(F/ℚ))
        (n : ℕ), 0 < n ∧ Module.finrank ℚ F = p ^ m ∧
        (∀ q : ℕ, q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)})) ∧
        K ⊔ ℚ⟮ξ n⟯ = F ⊔ ℚ⟮ξ n⟯ := by
  induction S using Finset.induction generalizing K with
  | empty => exact ⟨K, ‹_›, ‹_›, ‹_›, 1, Nat.one_pos, hK, by simpa using hram, rfl⟩
  | insert r S' hq ih =>
      by_cases hr₁ : r.Prime ∧ r ≠ p
      · by_cases hr₂ : Algebra.IsUnramifiedIn (𝓞 K) (span {(r : ℤ)})
        · refine ih K hK fun q hq₁ hq₂ hq₃ ↦ ?_
          by_cases hq : q = r
          · rwa [hq]
          · exact hram q hq₁ hq₂ (by grind)
        · obtain ⟨E, _, _, _, hE₁, hE₂, hE₃, hE₄⟩ :=
            kw_ramification_reduction hξ K m hm hK r hr₁.1 hr₁.2 hr₂
          have hunram (q : ℕ) (hq : Nat.Prime q) (hqp : q ≠ p)(hqS' :q ∉ S') :
              Algebra.IsUnramifiedIn (𝓞 E) (span {(q : ℤ)}) := by
            by_cases hqr : q = r
            · rwa [hqr]
            · exact hE₃ q hq (hram q hq hqp (by grind))
          obtain ⟨F, _, _, _, n, hn, hF₁, hF₂, hF₃⟩ := ih E hE₁ hunram
          have : NeZero n := NeZero.of_gt hn
          have : Fact r.Prime := ⟨hr₁.1⟩
          have : NeZero (n.lcm r) := ⟨Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
          refine ⟨F, ‹_›, ‹_›, ‹_›, n.lcm r, NeZero.pos _, hF₁, fun q hq hqp ↦  hF₂ q hq hqp, ?_⟩
          have : ℚ⟮ξ (n.lcm r)⟯ = ℚ⟮ξ n⟯ ⊔ ℚ⟮ξ r⟯ := by
            have := (hξ n).adjoinSimple_isCyclotomicExtension n ℚ A
            have := (hξ r).adjoinSimple_isCyclotomicExtension r ℚ A
            have := isCyclotomicExtension_lcm_sup ℚ A n r ℚ⟮ξ n⟯ ℚ⟮ξ r⟯
            have := (hξ (n.lcm r)).adjoinSimple_isCyclotomicExtension (n.lcm r) ℚ A
            exact IntermediateField.isCyclotomicExtension_eq {n.lcm r} ℚ A _ _
          rw [this, ← sup_assoc, sup_right_comm, hE₄, sup_right_comm, hF₃, sup_assoc]
      · refine ih K hK fun q hq₁ hq₂ hq₃ ↦ hram _ hq₁ hq₂ ?_
        rw [Finset.mem_insert, not_or]
        exact ⟨by grind, hq₃⟩

/-- Consumer of `kw_ramification_reduction`: iterating it over the finitely many primes `q ≠ p`
ramified in `K`, one obtains a cyclic `F/ℚ` of the same prime power degree, unramified outside `p`,
with `K ⊔ ℚ⟮ξ n⟯ = F ⊔ ℚ⟮ξ n⟯` for some `n` (so `K` is cyclotomic iff `F` is). The "unramified
outside `p`" condition is spelled out inline as `∀ q ≠ p prime, Algebra.IsUnramifiedIn (𝓞 F) (q)`. -/
lemma kw_reduce_to_unramified_outside_p {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A)
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] (m : ℕ) (hm : 0 < m) (hK : Module.finrank ℚ K = p ^ m) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (_ : IsGalois ℚ F) (_ : IsCyclic Gal(F/ℚ))
      (n : ℕ), 0 < n ∧ Module.finrank ℚ F = p ^ m ∧
      (∀ q : ℕ, q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)})) ∧
      K ⊔ ℚ⟮ξ n⟯ = F ⊔ ℚ⟮ξ n⟯ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ≠ p → q ∉ S →
      Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)}) := by
    refine ⟨(discr K).natAbs.primeFactors, fun q hq hpq hD ↦ ?_⟩
    refine (not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hq)).mp ?_
    contrapose! hD
    exact hq.mem_primeFactors (by rwa [← Int.natCast_dvd])
      (Int.natAbs_ne_zero.mpr <| discr_ne_zero K)
  exact kw_reduce_to_unramified_outside_p_aux ξ hξ m hm S K hK hS

end

end
