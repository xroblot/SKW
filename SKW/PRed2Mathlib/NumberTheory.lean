module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

@[expose] public section

/-!
# PRed to Mathlib: `emultiplicity` characterizations

The declarations in this file were extracted from `SKW.Prereqs.NumberTheory` and
submitted upstream as Mathlib PR
[#40301](https://github.com/leanprover-community/mathlib4/pull/40301).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.NumberTheory`) should be deleted, and any
usages redirected to the Mathlib versions.
-/

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

end
