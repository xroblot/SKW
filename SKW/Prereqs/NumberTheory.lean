module

public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Galois

@[expose] public section

open NumberField

/-! ### NumberField.Units -/

theorem NumberField.Units.natAbs_norm (K : Type*) [Field K] [NumberField K] (x : (RingOfIntegers K)ˣ) :
    (Algebra.norm ℤ x.val).natAbs = 1 := by
  apply Rat.natCast_injective
  rw [Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int, NumberField.Units.norm, Nat.cast_one]

theorem NumberField.isUnit_iff_natAbs_norm {K : Type*} [Field K] [NumberField K] {x : RingOfIntegers K} :
    IsUnit x ↔ (Algebra.norm ℤ x).natAbs = 1 := by
  rw [isUnit_iff_norm, ← Rat.natCast_injective.eq_iff, RingOfIntegers.coe_norm,
    Nat.cast_natAbs, Nat.cast_one, ← Algebra.coe_norm_int, Int.cast_abs]

/-! ### Galois / galRestrict -/

theorem smul_eq_galRestrict_apply (A : Type*) {K L B : Type*} [CommRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [CommRing B] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] (σ : Gal(L/K)) (x : B) :
    σ • x = galRestrict A K L B σ x := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [algebraMap.smul', AlgEquiv.smul_def, algebraMap_galRestrict_apply]

/-! ### Prime / WfDvdMonoid / UniqueFactorizationMonoid -/

theorem Prime.emultiplicity_self {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    [WfDvdMonoid α] {a : α} (ha : Prime a) : emultiplicity a a = 1 :=
  (FiniteMultiplicity.of_prime_left ha ha.ne_zero).emultiplicity_self

theorem Prime.emultiplicity_prime {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    [WfDvdMonoid α] [DecidableRel ((· ∣ ·) : α → α → Prop)] {p q : α} (hp : Prime p)
    (hq : Prime q) :
    emultiplicity p q = if Associated p q then 1 else 0 := by
  split_ifs with h
  · obtain ⟨u, rfl⟩ := h
    rw [emultiplicity_mul hp, hp.emultiplicity_self,
      emultiplicity_of_unit_right (hp.not_unit), add_zero]
  · rwa [emultiplicity_eq_zero, hp.dvd_prime_iff_associated hq]

theorem WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] [WfDvdMonoid R] {a p : R} (hp : Prime p) :
    a = 0 ↔ ∀ n, p ^ n ∣ a := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  by_contra!
  have := FiniteMultiplicity.of_prime_left hp this
  grind

theorem WfDvdMonoid.ne_zero_iff_finiteMultiplicity {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] [WfDvdMonoid R] {a p : R} (hp : Prime p) :
    a ≠ 0 ↔ FiniteMultiplicity p a := by
  convert (WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd hp).not
  rw [FiniteMultiplicity, not_forall]
  constructor
  · grind
  · intro ⟨n, hn⟩
    have hn' : 1 ≤ n := by
      contrapose! hn
      simp [Nat.lt_one_iff.mp hn, pow_zero]
    refine ⟨n - 1, by rwa [Nat.sub_add_cancel hn']⟩

theorem UniqueFactorizationMonoid.associated_iff_emultiplicity_eq {R : Type*}
    [CommMonoidWithZero R] [UniqueFactorizationMonoid R] {a b : R}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Associated a b ↔ ∀ (p : R), Prime p → emultiplicity p a = emultiplicity p b := by
  rw [← dvd_dvd_iff_associated, dvd_iff_emultiplicity_le ha, dvd_iff_emultiplicity_le hb,
    ← forall₂_and]
  simp_rw [le_antisymm_iff]

theorem UniqueFactorizationMonoid.associated_iff_emultiplicity_eq' {R : Type*}
    [CommMonoidWithZero R] [UniqueFactorizationMonoid R] (a b p : R) (hp : Prime p) :
    Associated a b ↔ ∀ (p : R), Prime p → emultiplicity p a = emultiplicity p b := by
  by_cases ha : a = 0
  · rw [ha, Associated.comm, associated_zero_iff_eq_zero]
    constructor
    · intro h
      simp [h]
    · intro h
      rw [WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd hp]
      specialize h p hp
      simp only [emultiplicity_zero] at h
      intro n
      rw [pow_dvd_iff_le_emultiplicity, ← h]
      exact le_top
  · by_cases hb : b = 0
    rw [hb, associated_zero_iff_eq_zero]
    constructor
    · intro h
      simp [h]
    · intro h
      rw [WfDvdMonoid.eq_zero_iff_forall_prime_pow_dvd hp]
      specialize h p hp
      simp only [emultiplicity_zero] at h
      intro n
      rw [pow_dvd_iff_le_emultiplicity, h]
      exact le_top
    · rw [← dvd_dvd_iff_associated, dvd_iff_emultiplicity_le ha, dvd_iff_emultiplicity_le hb,
        ← forall₂_and]
      simp_rw [le_antisymm_iff]

theorem UniqueFactorizationMonoid.eq_iff_emultiplicity_eq {R : Type*}
    [CommMonoidWithZero R] [UniqueFactorizationMonoid R] [Subsingleton Rˣ] [Infinite R]
    {a b : R} :
    a = b ↔ ∀ (p : R), Prime p → emultiplicity p a = emultiplicity p b := by
  obtain ⟨p, hp⟩ : ∃ p : R, Prime p := by
    rw [exists_prime_iff]
    obtain ⟨p, h⟩ := Set.Finite.exists_notMem (Set.toFinite ({0, 1} : Set R))
    refine ⟨p, by grind, ?_⟩
    by_contra! hp
    lift p to Rˣ using hp
    simp [Subsingleton.elim p 1] at h
  rw [← associated_iff_eq, associated_iff_emultiplicity_eq' _ _ p hp]

/-! ### ZMod -/

theorem ZMod.orderOf_mod_self_pow_sub_one (a k : ℕ) (ha : 1 < a) :
    orderOf (a : ZMod (a ^ k - 1)) = k := by
  have h₁ {n : ℕ} (hn : 0 < n) : 2 ≤ a ^ n := (Nat.le_pow hn).trans <| Nat.pow_le_pow_left ha n
  have h₂ {a k b : ℕ} (hb : 1 ≤ b) : (b : ZMod (a ^ k - 1)) = 1 ↔ a ^ k - 1 ∣ b - 1 := by
    rw [← Nat.cast_one (R := ZMod (a ^ k - 1)), ZMod.natCast_eq_natCast_iff,
      Nat.ModEq.comm, Nat.modEq_iff_dvd, ← Nat.cast_sub hb, Int.natCast_dvd_natCast]
  obtain rfl | hk := Nat.eq_zero_or_pos k
  · refine orderOf_eq_zero_iff'.mpr fun n hn ↦ ?_
    rw [← Nat.cast_pow, ne_eq, h₂ (one_le_two.trans (h₁ hn)), pow_zero, tsub_self, zero_dvd_iff]
    grind
  refine (orderOf_eq_iff hk).mpr ⟨?_, fun m hm hm' ↦ ?_⟩
  · rw [← Nat.cast_pow, h₂ (one_le_two.trans (h₁ hk))]
  · rw [← Nat.cast_pow, ne_eq, h₂ (one_le_two.trans (h₁ hm'))]
    refine Nat.not_dvd_of_pos_of_lt (by aesop) ?_
    rwa [Nat.sub_lt_sub_iff_right (one_le_two.trans (h₁ hm')), Nat.pow_lt_pow_iff_right ha]
