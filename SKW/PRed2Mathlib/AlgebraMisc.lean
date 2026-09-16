module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# PRed to Mathlib: maximal subgroups of abelian `p`-groups

The declarations in this file were extracted from `SKW.Prereqs.AlgebraMisc` and submitted upstream as
Mathlib PR [#41652](https://github.com/leanprover-community/mathlib4/pull/41652):
`CommGroup.isCoatom_iff_index_eq_prime`, `IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic`.

Once that PR merges and the `lake-manifest.json` pin is bumped past the merge commit, this file (and
its import in `SKW.Prereqs.AlgebraMisc`) should be deleted, and any usages redirected to the Mathlib
versions.
-/

@[expose] public section

open Subgroup in
/-- In an abelian `p`-group (finite or infinite), the maximal subgroups are exactly the subgroups
of index `p`. -/
theorem CommGroup.isCoatom_iff_index_eq_prime {G : Type*} [CommGroup G] {p : ℕ} [hp : Fact p.Prime]
    (hG : IsPGroup p G) (M : Subgroup G) : IsCoatom M ↔ M.index = p := by
  rw [← CommGroup.isSimpleGroup_iff_isCoatom, CommGroup.is_simple_iff_prime_card,
    Subgroup.index_eq_card]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hp.out⟩
  have h_dvd := (IsPGroup.card_eq_or_dvd (hG.to_quotient M)).resolve_left h.ne_one
  exact ((Nat.prime_dvd_prime_iff_eq hp.out h).mp h_dvd).symm

open Subgroup in
/-- A finite non-cyclic abelian `p`-group has two distinct subgroups of index `p`. -/
theorem IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic {G : Type*} [CommGroup G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hnc : ¬ IsCyclic G) :
    ∃ H₁ H₂ : Subgroup G, H₁.index = p ∧ H₂.index = p ∧ H₁ ≠ H₂ := by
  by_contra hcon
  push Not at hcon
  refine hnc (isCyclic_of_isCoatom_subsingleton fun M₁ M₂ hM₁ hM₂ => ?_)
  exact hcon M₁ M₂ ((CommGroup.isCoatom_iff_index_eq_prime hG M₁).mp hM₁)
    ((CommGroup.isCoatom_iff_index_eq_prime hG M₂).mp hM₂)

end
