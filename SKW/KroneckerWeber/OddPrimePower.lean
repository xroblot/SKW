module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.ZMod.UnitsCyclic

public import SKW.KroneckerWeber.Basic
public import SKW.KroneckerWeber.ClassGroup
public import SKW.KroneckerWeber.Reduction
public import SKW.Prereqs.Unramified
public import SKW.Prereqs.NumberField

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

open NumberField Ideal IntermediateField IsCyclotomicExtension

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime] [hp' : Fact (Odd p)]

set_option backward.isDefEq.respectTransparency false in
open IntermediateField in
/-- Every cyclic extension of `ℚ` of odd prime power degree `pᵐ` unramified outside `p` is
cyclotomic: contained in `ℚ(ζ_{p^{m+1}}) = ℚ⟮ξ (p^(m+1))⟯` inside the ambient field `A`. -/
theorem prop_kw_odd_prime_power {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ) (hm : 0 < m) (K : IntermediateField ℚ A)
    [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)] (hK : Module.finrank ℚ K = p ^ m)
    (hKram : UnramifiedOutside K p) :
    K ≤ ℚ⟮ξ (p ^ (m + 1))⟯ := by
  -- `C = ℚ(ζ_{p^{m+1}})` is a cyclic cyclotomic extension of `ℚ` (odd `p`) of degree `pᵐ·(p-1)`,
  -- totally ramified at `p` and unramified outside `p`.
  let C : IntermediateField ℚ A := ℚ⟮ξ (p ^ (m + 1))⟯
  have hC : IsCyclotomicExtension {p ^ (m + 1)} ℚ C := sorry
  have : IsAbelianGalois ℚ C := sorry
  have : NumberField C := sorry
  -- (1) `C` has a (unique) subfield `K'` of degree `pᵐ` over `ℚ`; being a subfield of the cyclic,
  --     unramified-outside-`p` field `C`, it is itself cyclic and unramified outside `p`.
  obtain ⟨K', hK'₁, hK'₂, hK'₃, hK'₄⟩ :
      ∃ K' : IntermediateField ℚ A, K' ≤ C ∧ Module.finrank ℚ K' = p ^ m ∧
        IsCyclic Gal(K'/ℚ) ∧ UnramifiedOutside K' p := by
    have : IsCyclic Gal(C/ℚ) := by
      rw [(Rat.galEquivZMod (p ^ (m + 1)) C).isCyclic]
      exact ZMod.isCyclic_units_of_prime_pow _ hp.out (by grind [hp'.out]) _
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(C/ℚ))
    have hC : Nat.card Gal(C/ℚ) = p ^ m * (p - 1) := by
      rw [IsGalois.card_aut_eq_finrank, Rat.finrank (p ^ (m + 1)),
        Nat.totient_prime_pow hp.out (by positivity), add_tsub_cancel_right]
    refine ⟨lift (fixedField (Subgroup.zpowers (σ ^ (p ^ m)))), lift_le _, ?_, ?_, ?_⟩
    · rw [finrank_lift, fixedField, IsGaloisGroup.finrank_fixedPoints_eq_index_subgroup,
        Subgroup.index_eq_iff_card_mul_eq_card, Nat.card_zpowers,
        orderOf_pow_of_orderOf_eq_mul (orderOf_pos σ) (by rw [hσ, hC]),
        IsGalois.card_aut_eq_finrank, Rat.finrank (p ^ (m + 1)),
        Nat.totient_prime_pow hp.out (by positivity), add_tsub_cancel_right, mul_comm]
    · rw [(liftAlgEquiv _).symm.autCongr.isCyclic, ← (IsGalois.normalAutEquivQuotient _).isCyclic]
      apply isCyclic_of_surjective _ (QuotientGroup.mk'_surjective _)
    · intro q hq hqp
      have : Fact q.Prime := ⟨hq⟩
      apply Algebra.IsUnramifiedIn.of_algEquiv <|
        RingOfIntegers.mapIntAlgEquiv (liftAlgEquiv _).toRingEquiv
      refine Algebra.IsUnramifiedIn.tower_bot (T := 𝓞 C) fun Q hQ₁ hQ₂ ↦
        ramificationIdx'_eq_one_iff.mp ?_
      rw [Rat.ramificationIdx_eq_of_not_dvd q (m := p ^ (m + 1))]
      intro h
      exact hqp <| (Nat.prime_dvd_prime_iff_eq hq hp.out).mp <| hq.dvd_of_dvd_pow h
  -- (2) The compositum `K ⊔ K'` is cyclic: otherwise `Gal((K ⊔ K')/ℚ)`, an abelian subgroup of
  --     `ℤ/pᵐ × ℤ/pᵐ`, would surject onto `(ℤ/p)²`, yielding two independent degree-`p`
  --     subextensions unramified outside `p` — impossible by `prop_kw_exponent_p` (uniqueness of
  --     the degree-`p` extension unramified outside `p`).
  have : NumberField K' := by
    let : Algebra K' C := (inclusion hK'₁).toAlgebra
    exact NumberField.of_tower ℚ C _
  have : IsGalois ℚ K' := sorry
  have hMcyc : IsCyclic Gal(↑(K ⊔ K')/ℚ) := sorry
  -- (3) `[K:ℚ] = [K':ℚ] = pᵐ`, so in the cyclic `K ⊔ K'`, `kw_cyclic_compositum` forces `K ≤ K'`
  --     (and by symmetry `K = K'`); then `K ≤ K' ≤ C`.
  have hKK' : K ≤ K' := by
    have := kw_cyclic_compositum ↑(K ⊔ K') (K.restrict le_sup_left) (K'.restrict le_sup_right)
      (by rw [finrank_restrict, finrank_restrict, hK, hK'₂])
    rwa [restrict_le_restrict_iff] at this
  exact hKK'.trans hK'₁

end

end
