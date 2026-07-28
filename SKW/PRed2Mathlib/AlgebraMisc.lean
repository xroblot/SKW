module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# PRed to Mathlib: `IsCyclic.subgroup_le/eq_subgroup_iff`

The declarations in this file were extracted from `SKW.Prereqs.AlgebraMisc` and submitted
upstream as Mathlib PR [#40597](https://github.com/leanprover-community/mathlib4/pull/40597).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.AlgebraMisc`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

@[expose] public section

theorem Int.zmultiples_sup_zmultiples (a b : ℤ) :
    AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b = AddSubgroup.zmultiples (a.gcd b : ℤ) := by
  rw [AddSubgroup.zmultiples_eq_closure, AddSubgroup.zmultiples_eq_closure,
    ← AddSubgroup.closure_union, Set.singleton_union, Int.closure_eq_zmultiples]

theorem Int.zmultiples_le_zmultiples (a b : ℤ) :
    AddSubgroup.zmultiples a ≤ AddSubgroup.zmultiples b ↔ b ∣ a := by
  rw [AddSubgroup.zmultiples_le, mem_zmultiples_iff]

theorem AddSubgroup.zmultiples_le_zmultiples_iff {G : Type*} [AddGroup G] (g : G) (i j : ℤ) :
    AddSubgroup.zmultiples (i • g) ≤ AddSubgroup.zmultiples (j • g) ↔
      j.gcd (addOrderOf g) ∣ i.gcd (addOrderOf g) := by
  rw [← zmultiplesHom_apply, ← AddMonoidHom.map_zmultiples, ← zmultiplesHom_apply,
    ← AddMonoidHom.map_zmultiples, AddSubgroup.map_le_map_iff', zmultiplesHom_ker_eq,
    Int.zmultiples_sup_zmultiples, Int.zmultiples_sup_zmultiples, Int.zmultiples_le_zmultiples,
    Int.natCast_dvd_natCast]

@[to_additive existing]
theorem Subgroup.zpowers_le_zpowers_iff {G : Type*} [Group G] (g : G) (i j : ℤ) :
    Subgroup.zpowers (g ^ i) ≤ Subgroup.zpowers (g ^ j) ↔
      j.gcd (orderOf g) ∣ i.gcd (orderOf g) := by
  rw [← SetLike.coe_subset_coe, ← Additive.ofMul.image_subset,
    ofMul_image_zpowers_eq_zmultiples_ofMul, ofMul_image_zpowers_eq_zmultiples_ofMul,
    SetLike.coe_subset_coe, ofMul_zpow, ofMul_zpow, AddSubgroup.zmultiples_le_zmultiples_iff,
    addOrderOf_ofMul_eq_orderOf]

@[to_additive]
theorem Subgroup.zpowers_eq_zpowers_iff' {G : Type*} [Group G] (g : G) (i j : ℤ) :
    Subgroup.zpowers (g ^ i) = Subgroup.zpowers (g ^ j) ↔
      i.gcd (orderOf g) = j.gcd (orderOf g) := by
  rw [le_antisymm_iff, Subgroup.zpowers_le_zpowers_iff, Subgroup.zpowers_le_zpowers_iff,
    dvd_dvd_iff_associated, associated_iff_eq, eq_comm]

theorem Subgroup.zpowers_zpow_sup {G : Type*} [Group G] (g : G) (i j : ℤ) :
    Subgroup.zpowers (g ^ i) ⊔ Subgroup.zpowers (g ^ j) = Subgroup.zpowers (g ^ (i.gcd j : ℤ)) := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers_iff.2 ⟨i / (i.gcd j : ℤ),
      by rw [← zpow_mul, Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)]⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers_iff.2 ⟨j / (i.gcd j : ℤ),
      by rw [← zpow_mul, Int.mul_ediv_cancel' (Int.gcd_dvd_right ..)]⟩
  · rw [Subgroup.zpowers_le]
    have h : (g ^ i) ^ Int.gcdA i j * (g ^ j) ^ Int.gcdB i j = g ^ (i.gcd j : ℤ) := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← Int.gcd_eq_gcd_ab]
    rw [← h]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩)
      (Subgroup.mem_zpowers_iff.2 ⟨_, rfl⟩)

theorem Nat.div_dvd_div_iff {k m n : ℕ} (hk : 0 < k) (hm : 0 < m) (hmk : m ∣ k) (hnk : n ∣ k) :
    k / m ∣ k / n ↔ n ∣ m := by
  rw [Nat.div_dvd_iff_dvd_mul hmk hm, ← Nat.mul_div_assoc _ hnk,
    Nat.dvd_div_iff_mul_dvd (hnk.mul_left m), Nat.mul_dvd_mul_iff_right hk]

@[to_additive]
theorem Subgroup.map_top {G : Type*} [Group G] {N : Type*} [Group N] (f : G →* N) :
    Subgroup.map f ⊤ = f.range :=
  (MonoidHom.range_eq_map f).symm

@[to_additive]
theorem Subgroup.exists_zpowers_eq_top_of_zpowers_eq_top {G : Type*} [Group G] {g : G}
    (hg : Subgroup.zpowers g = ⊤) (H : Subgroup G) :
    ∃ i : ℤ, Subgroup.zpowers (g ^ i) = H := by
  have : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, hg⟩
  obtain ⟨⟨x, hx⟩, hx'⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := H)).mp inferInstance
  obtain ⟨i, rfl⟩ := (Subgroup.eq_top_iff' _).mp hg x
  exact ⟨i, by simpa [Subgroup.map_top] using (congr_arg (Subgroup.map H.subtype) hx')⟩

@[to_additive]
theorem orderOf_pow_natAbs {G : Type*} [Group G] {x : G} (n : ℤ) :
    orderOf (x ^ n.natAbs) = orderOf (x ^ n) := by
  obtain ⟨a, (rfl | rfl)⟩ := Int.eq_nat_or_neg n
  · simp
  · simp

@[to_additive]
theorem orderOf_zpow {G : Type*} [Group G] [Finite G] {n : ℤ} (x : G) :
    orderOf (x ^ n) = orderOf x / (orderOf x).gcd n.natAbs := by
  rw [← orderOf_pow, orderOf_pow_natAbs]

@[to_additive]
theorem orderOf_zpow' {G : Type*} [Group G] (x : G) {n : ℤ} (h : n ≠ 0) :
    orderOf (x ^ n) = orderOf x / (orderOf x).gcd n.natAbs := by
  rw [← orderOf_pow' _ (Int.natAbs_ne_zero.mpr h), orderOf_pow_natAbs]

@[to_additive]
theorem IsCyclic.subgroup_le_subgroup_iff {G : Type*} [Group G] [Finite G] [hG : IsCyclic G]
    {H K : Subgroup G} :
    H ≤ K ↔ Nat.card H ∣ Nat.card K := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  obtain ⟨i, rfl⟩ := Subgroup.exists_zpowers_eq_top_of_zpowers_eq_top hg H
  obtain ⟨j, rfl⟩ := Subgroup.exists_zpowers_eq_top_of_zpowers_eq_top hg K
  rw [Subgroup.zpowers_le_zpowers_iff, Nat.card_zpowers, orderOf_zpow, Nat.card_zpowers, orderOf_zpow,
    Nat.div_dvd_div_iff (orderOf_pos g) (Nat.gcd_pos_of_pos_left _ (orderOf_pos g))
    (Nat.gcd_dvd_left (orderOf g) _) (Nat.gcd_dvd_left (orderOf g) _), Int.gcd_eq_natAbs,
    Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.gcd_comm, Nat.gcd_comm _ (orderOf g)]

@[to_additive]
theorem IsCyclic.subgroup_eq_subgroup_iff {G : Type*} [Group G] [Finite G] [hG : IsCyclic G]
    {H K : Subgroup G} :
    H = K ↔ Nat.card H = Nat.card K := by
  rw [le_antisymm_iff, subgroup_le_subgroup_iff, subgroup_le_subgroup_iff, dvd_dvd_iff_associated,
    associated_iff_eq]

end

/-!
# PRed to Mathlib: `IntermediateField.adjoin_simple_add` / `adjoin_simple_mul`

The declarations in this file were extracted from `SKW.Prereqs.AlgebraMisc` and submitted
upstream as Mathlib PR [#41649](https://github.com/leanprover-community/mathlib4/pull/41649)
(there renamed `IntermediateField.adjoin_simple_add_algebraMap` /
`IntermediateField.adjoin_simple_mul_algebraMap`).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.AlgebraMisc`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

@[expose] public section

theorem IntermediateField.adjoin_simple_add {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (y : F) : adjoin F {x + algebraMap F E y} = adjoin F {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact add_mem (mem_adjoin_simple_self F x) (algebraMap_mem _ y)
  · rw [adjoin_simple_le_iff]
    convert IntermediateField.sub_mem _ (mem_adjoin_simple_self F _) (algebraMap_mem _ y)
    rw [eq_sub_iff_add_eq]

theorem IntermediateField.adjoin_simple_mul {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (y : F) (hy : y ≠ 0) : adjoin F {x * algebraMap F E y} = adjoin F {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact mul_mem (mem_adjoin_simple_self F x) (algebraMap_mem _ y)
  · rw [adjoin_simple_le_iff]
    convert IntermediateField.div_mem _ (mem_adjoin_simple_self F _) (algebraMap_mem _ y)
    rw [mul_div_cancel_right₀ x (by rwa [map_ne_zero])]

end

/-!
# PRed to Mathlib: coatoms of the subgroup lattice and abelian `p`-groups

The declarations in this file were extracted from `SKW.Prereqs.AlgebraMisc` and submitted upstream as
two stacked Mathlib PRs:
* [#41651](https://github.com/leanprover-community/mathlib4/pull/41651): `comapMk'OrderIso'`,
  `isCyclic_of_isCoatom_subsingleton`, `CommGroup.isSimpleGroup_iff_isCoatom`.
* [#41652](https://github.com/leanprover-community/mathlib4/pull/41652): `CommGroup.isCoatom_iff_index_eq_prime`,
  `IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic`.

Once those PRs merge and the `lake-manifest.json` pin is bumped past the merge commits, this file (and
its import in `SKW.Prereqs.AlgebraMisc`) should be deleted, and any usages redirected to the Mathlib
versions.
-/

@[expose] public section

open Subgroup in
/-- A group with at most one maximal subgroup is cyclic. Maximal subgroups are the coatoms
`IsCoatom (· : Subgroup G)` of the subgroup lattice. Only `IsCoatomic (Subgroup G)` is required
(automatic for finite `G`); no finiteness, commutativity, or `p`-group hypothesis is needed. -/
theorem isCyclic_of_isCoatom_subsingleton {G : Type*} [Group G] [IsCoatomic (Subgroup G)]
    (h : ∀ M₁ M₂ : Subgroup G, IsCoatom M₁ → IsCoatom M₂ → M₁ = M₂) :
    IsCyclic G := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  obtain hbot | ⟨M, hM, -⟩ := eq_top_or_exists_le_coatom (⊥ : Subgroup G)
  · exact ⟨1, eq_top_of_bot_eq_top hbot _⟩
  · obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt hM.lt_top
    refine ⟨g, ?_⟩
    by_contra hne
    obtain ⟨M', hM', hle⟩ := (eq_top_or_exists_le_coatom (zpowers g)).resolve_left hne
    exact hg (h M' M hM' hM ▸ hle (mem_zpowers g))

/-- The correspondence theorem as an order isomorphism `Subgroup (G ⧸ N) ≃o Set.Ici N`. -/
@[simps apply_coe]
def QuotientGroup.comapMk'OrderIso' {G : Type*} [Group G] (N : Subgroup G) [hn : N.Normal] :
    Subgroup (G ⧸ N) ≃o Set.Ici N where
  toFun H' := ⟨Subgroup.comap (mk' N) H', le_comap_mk' N _⟩
  invFun H := Subgroup.map (mk' N) H
  left_inv H' := Subgroup.map_comap_eq_self <| by simp
  right_inv := fun ⟨H, hH⟩ => Subtype.ext <| by simpa
  map_rel_iff' := Subgroup.comap_le_comap_of_surjective <| mk'_surjective _

/-- A subgroup of a commutative group is maximal (a coatom in the subgroup lattice) iff the quotient
by it is simple. Group analogue of `isSimpleModule_iff_isCoatom`. -/
theorem CommGroup.isSimpleGroup_iff_isCoatom {G : Type*} [CommGroup G] {M : Subgroup G} :
    IsSimpleGroup (G ⧸ M) ↔ IsCoatom M := by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom,
    ← (QuotientGroup.comapMk'OrderIso' M).isSimpleOrder_iff, isSimpleGroup_iff, isSimpleOrder_iff]
  by_cases hG : Nontrivial (G ⧸ M)
  · simp [hG, Subgroup.normal_of_isMulCommutative]
  · simp [hG]

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
