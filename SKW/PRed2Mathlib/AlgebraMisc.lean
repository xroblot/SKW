module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

/-!
# PRed to Mathlib: `RingEquiv.toRatAlgEquiv` / `RingEquiv.toIntAlgEquiv`

The declarations in this file were extracted from `SKW.Prereqs.AlgebraMisc` and submitted
upstream as Mathlib PR [#40298](https://github.com/leanprover-community/mathlib4/pull/40298).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.AlgebraMisc`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

variable {R S : Type*}

/-- Reinterpret a `RingEquiv as a `ℚ`-algebra isomorphism. This actually yields an equivalence,
see `RingEquiv.equivRatAlgEquiv`. -/
def RingEquiv.toRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) : R ≃ₐ[ℚ] S :=
  { f with commutes' := f.toRingHom.map_rat_algebraMap }

@[simp]
theorem RingEquiv.toRatAlgEquiv_toRingEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) :
    ↑f.toRatAlgEquiv = f :=
  RingEquiv.ext fun _ ↦ rfl

@[simp]
theorem RingEquiv.toRatAlgEquiv_apply [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) (x : R) :
    f.toRatAlgEquiv x = f x :=
  rfl

@[simp]
theorem AlgEquiv.toRingEquiv_toRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R ≃ₐ[ℚ] S) : (f : R ≃+* S).toRatAlgEquiv = f :=
  AlgEquiv.ext fun _ => rfl

/-- The equivalence between `RingEquiv` and `ℚ`-algebra isomorphisms. -/
def RingEquiv.equivRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] :
    (R ≃+* S) ≃ (R ≃ₐ[ℚ] S) where
  toFun := RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv
  left_inv f := RingEquiv.toRatAlgEquiv_toRingEquiv f
  right_inv f := AlgEquiv.toRingEquiv_toRatAlgEquiv f

/-- Reinterpret a `RingEquiv` as a `ℤ`-algebra isomorphism. -/
def RingEquiv.toIntAlgEquiv [Ring R] [Ring S] (f : R ≃+* S) : R ≃ₐ[ℤ] S :=
  { f with commutes' := fun n ↦ by simp }

@[simp]
lemma RingEquiv.toIntAlgEquiv_coe [Ring R] [Ring S] (f : R ≃+* S) :
    ⇑f.toIntAlgEquiv = ⇑f := rfl

lemma RingEquiv.toIntAlgEquiv_apply [Ring R] [Ring S] (f : R ≃+* S) (x : R) :
    f.toIntAlgEquiv x = f x := rfl

lemma RingEquiv.toIntAlgEquiv_injective [Ring R] [Ring S] :
    Function.Injective (RingEquiv.toIntAlgEquiv : (R ≃+* S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

end

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

end
