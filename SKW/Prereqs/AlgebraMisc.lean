module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public import SKW.PRed2Mathlib.AlgebraMisc

@[expose] public section

theorem Int.zmultiples_sup_zmultiples (a b : ℤ) :
    AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b = AddSubgroup.zmultiples (a.gcd b : ℤ) := by
  rw [AddSubgroup.zmultiples_eq_closure, AddSubgroup.zmultiples_eq_closure,
    ← AddSubgroup.closure_union, Set.singleton_union, Int.closure_eq_zmultiples]

theorem Int.zmultiples_le_zmultiples (a b : ℤ) :
    AddSubgroup.zmultiples a ≤ AddSubgroup.zmultiples b ↔ b ∣ a := by
  rw [AddSubgroup.zmultiples_le,  mem_zmultiples_iff]

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

@[simp]
theorem Subgroup.map_top {G : Type*} [Group G] {N : Type*} [Group N] (f : G →* N) :
    map f ⊤ = f.range := (MonoidHom.range_eq_map f).symm

theorem Nat.dvd_div_dvd_iff {a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (h₁ : b ∣ a) (h₂ : d ∣ a) :
    a / b ∣ a / d ↔ d ∣ b := by
  rw [Nat.div_dvd_iff_dvd_mul h₁ hb, ← Nat.mul_div_assoc _ h₂, Nat.dvd_div_iff_mul_dvd (h₂.mul_left b),
    Nat.mul_dvd_mul_iff_right ha]

theorem IsCyclic.subgroup_le_subgroup_iff {G : Type*} [Group G] [Finite G] [hG : IsCyclic G]
    {H K : Subgroup G} :
    H ≤ K ↔ Nat.card H ∣ Nat.card K := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := G)
  obtain ⟨⟨x, _⟩, hx'⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := H)).mp inferInstance
  obtain ⟨⟨y, _⟩, hy'⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := K)).mp inferInstance
  obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hg x)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hg y)
  have Heq : H = Subgroup.zpowers (g ^ i) := by
    simpa [MonoidHom.map_zpowers, Subgroup.subtype_apply, eq_comm] using
      congr_arg (Subgroup.map H.subtype) hx'
  rw [Heq]
  have Keq : K = Subgroup.zpowers (g ^ j) := by
    simpa [MonoidHom.map_zpowers, Subgroup.subtype_apply, eq_comm] using
      congr_arg (Subgroup.map K.subtype) hy'
  rw [Keq, ← zpow_natCast, ← zpow_natCast, Subgroup.zpowers_le_zpowers_iff,
    Nat.card_zpowers, zpow_natCast, orderOf_pow, Nat.card_zpowers, zpow_natCast, orderOf_pow]
  rw [Nat.dvd_div_dvd_iff, Nat.gcd_comm _ i, Nat.gcd_comm _ j]
  rw [Int.gcd_natCast_natCast, Int.gcd_natCast_natCast]
  exact orderOf_pos g
  exact Nat.gcd_pos_of_pos_left i (orderOf_pos g)
  exact Nat.gcd_dvd_left (orderOf g) i
  exact Nat.gcd_dvd_left (orderOf g) j

theorem IsCyclic.subgroup_eq_subgroup_iff {G : Type*} [Group G] [Finite G] [hG : IsCyclic G]
    {H K : Subgroup G} :
    H = K ↔ Nat.card H = Nat.card K := by
  rw [le_antisymm_iff, subgroup_le_subgroup_iff, subgroup_le_subgroup_iff, dvd_dvd_iff_associated,
    associated_iff_eq]

/-! ### MulEquiv / AlgHom / AlgEquiv -/

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

end
