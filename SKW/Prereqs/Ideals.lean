module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.RamificationInertia.Ramification

@[expose] public section

open NumberField

/-! ### Ideal -/

theorem Ideal.absNorm_eq_card {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] (I : Ideal S) :
    Ideal.absNorm I = Nat.card (S ⧸ I) := rfl

-- theorem Ideal.isCoprime_of_coprime_absNorm {S : Type*} [CommRing S] [IsDedekindDomain S]
--     [Module.Free ℤ S] {I J : Ideal S} (h : I.absNorm.Coprime J.absNorm) :
--     IsCoprime I J := by
--   refine isCoprime_iff_exists.mpr ⟨(absNorm I) * (absNorm I).gcdA (absNorm J), ?_,
--     (absNorm J) * (absNorm I).gcdB (absNorm J), ?_, ?_⟩
--   · exact mul_mem_right _ I (absNorm_mem I)
--   · exact mul_mem_right _ J (absNorm_mem J)
--   · simp only [← Int.cast_natCast (R := S), ← Int.cast_mul, ← Int.cast_add,
--       ← Nat.gcd_eq_gcd_ab I.absNorm J.absNorm, h, Nat.cast_one, Int.cast_one]

theorem Ideal.multiplicity_top {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ≠ ⊤) :
    multiplicity I ⊤ = 0 := by
  rw [← one_eq_top, multiplicity_of_one_right (by rwa [Ideal.isUnit_iff])]

theorem Ideal.emultiplicity_top {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ≠ ⊤) :
    emultiplicity I ⊤ = 0 := by
  rw [← one_eq_top, emultiplicity_of_one_right (by rwa [Ideal.isUnit_iff])]

@[simps]
def Ideal.mapEquiv {R S F : Type*} [CommSemiring R] [CommSemiring S] [EquivLike F R S]
    [RingHomClass F R S]  (e : F) : Ideal R ≃+* Ideal S where
  toFun := Ideal.map e
  invFun := Ideal.comap e
  __ := Ideal.mapHom e
  left_inv _ := by simpa using comap_map_of_bijective _ (EquivLike.bijective e)
  right_inv _ := by simpa using Ideal.map_comap_of_surjective _ (EquivLike.surjective e) _

open Pointwise in
theorem Ideal.pointwise_smul_def' {M R : Type*} [Group M] [CommSemiring R] [MulSemiringAction M R] {a : M}
    (S : Ideal R) :
    a • S = mapEquiv (MulSemiringAction.toRingEquiv M R a) S := rfl

theorem Ideal.infinite_of_not_isField {R : Type*} [CommRing R] [Nontrivial R]
    [IsCancelMulZero (Ideal R)] (h : ¬IsField R) :
    Infinite (Ideal R) := by
  obtain ⟨I, h₁, h₂⟩ := Ring.not_isField_iff_exists_prime.mp h
  apply Infinite.of_injective (fun n : ℕ ↦ I ^ n)
  intro n m hI
  dsimp at hI
  by_contra! h
  obtain h | h := Nat.ne_iff_lt_or_gt.mp h
  · obtain ⟨t, ht, rfl⟩ := lt_iff_exists_add.mp h
    rw [pow_add, left_eq_mul₀ (pow_ne_zero n h₁), Ideal.one_eq_top, Ideal.pow_eq_top_iff] at hI
    exact h₂.ne_top <| hI.resolve_right ht.ne'
  · obtain ⟨t, ht, rfl⟩ := lt_iff_exists_add.mp h
    rw [pow_add, mul_eq_left₀ (pow_ne_zero m h₁), Ideal.one_eq_top, Ideal.pow_eq_top_iff] at hI
    exact h₂.ne_top <| hI.resolve_right ht.ne'

instance (K : Type*) [Field K] [NumberField K] :
    Infinite (Ideal (𝓞 K)) :=
  Ideal.infinite_of_not_isField (RingOfIntegers.not_isField K)

/-! ### Ideal — LiesOver / ramification -/

theorem Ideal.pow_liesOver_of_liesOver {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S) [P.LiesOver p]
    {i : ℕ} (hi : i + 1 ≤ Ideal.ramificationIdx p P) :
    (P ^ (i + 1)).LiesOver p := by
  rw [liesOver_iff]
  apply le_antisymm
  · exact le_trans le_comap_pow_ramificationIdx <| comap_mono (pow_le_pow_right hi)
  · refine le_trans (comap_mono <| pow_le_pow_right (Nat.le_add_left 1 i)) ?_
    rw [pow_one, ← Ideal.under_def, ← Ideal.over_def P p]

instance Ideal.Quotient.isScalarTower_of_liesOver_liesOver {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (Q : Ideal C)
    (P : Ideal B) (p : Ideal A) [Q.LiesOver P] [P.LiesOver p] [Q.LiesOver p] :
    IsScalarTower (A ⧸ p) (B ⧸ P) (C ⧸ Q) := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ Quotient.inductionOn' x fun x ↦ ?_
  have : Quotient.mk'' x = Ideal.Quotient.mk p x := rfl
  simp [this, Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]

theorem Ideal.liesOver_of_absNorm_dvd_prime_pow {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Algebra.IsIntegral ℤ R] (I : Ideal R) [I.IsPrime] {p k : ℕ}
    [hp : Fact (Nat.Prime p)] (hI : Ideal.absNorm I ∣ p ^ k) :
    I.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : NeZero I := ⟨by
    contrapose! hI
    rw [hI, map_zero, Nat.zero_dvd]
    exact NeZero.ne (p ^ k)⟩
  have := (Int.absNorm_under_dvd_absNorm I).trans hI
  rw [Ideal.liesOver_iff, ← Nat.prime_eq_prime_of_dvd_pow (Nat.absNorm_under_prime I)
    hp.out this, Int.ideal_span_absNorm_eq_self]

theorem Algebra.not_isUnramifiedAt_iff_of_isDedekindDomain {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {p : Ideal S} [p.IsPrime] [IsDedekindDomain S] [Module.Finite R S] [IsDomain R]
    [Module.IsTorsionFree R S] [Module.Finite ℤ R] [CharZero R] (hp : p ≠ ⊥) :
    ¬ IsUnramifiedAt R p ↔ 1 < (Ideal.under R p).ramificationIdx p := by
  rw [isUnramifiedAt_iff_of_isDedekindDomain hp, ne_iff_gt_iff_ge, Order.one_le_iff_pos,
    Ideal.ramificationIdx_eq_ramificationIdx' _ _ (Ideal.under_ne_bot R hp)]
  exact Ideal.ramificationIdx'_pos _ _

/-! ### Ideal — IsDedekindDomain / emultiplicity -/

theorem Ideal.IsDedekindDomain.prime_of_maximal {R : Type*} [CommRing R] [CharZero R]
    [Algebra.IsIntegral ℤ R] [IsDedekindDomain R] (I : Ideal R) [I.IsMaximal] :
    Prime I := by
  refine (prime_iff_isPrime (IsMaximal.ne_bot_of_isIntegral_int I)).mpr <| IsMaximal.isPrime' I

-- Replace Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul?
theorem Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul' {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R] [FaithfulSMul R S]
    {v : Ideal R} {w : Ideal S} (I : Ideal R) (hv : Irreducible v) (hw : Irreducible w)
    (hw_bot : w ≠ ⊥) [w.LiesOver v] :
    emultiplicity w (map (algebraMap R S) I) = v.ramificationIdx w * emultiplicity v I := by
  by_cases hI : I = ⊥
  · rw [hI, map_bot, ← zero_eq_bot, ← zero_eq_bot, emultiplicity_zero, emultiplicity_zero, ENat.mul_top]
    simp only [ne_eq, Nat.cast_eq_zero]
    apply ramificationIdx_ne_zero (map_ne_bot_of_ne_bot <| hv.ne_zero) (isPrime_of_prime hw.prime)
    rw [map_le_iff_le_comap, over_def w v]
  · exact emultiplicity_map_eq_ramificationIdx_mul hI hv hw hw_bot

theorem Ideal.IsDedekindDomain.ramificationIdx_mul_emultiplicity_under_eq {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] {w : Ideal S} (hw : Irreducible w) (hw_bot : w ≠ ⊥) {I : Ideal R} :
    (under R w).ramificationIdx w * emultiplicity (under R w) I =
        emultiplicity w (map (algebraMap R S) I) := by
  have : w.IsPrime := (prime_iff_isPrime hw_bot).mp hw.prime
  have : Irreducible (comap (algebraMap R S) w) :=
    irreducible_iff_prime.mpr <|
      (prime_iff_isPrime (under_ne_bot R hw_bot)).mpr (IsPrime.under R w)
  exact (emultiplicity_map_eq_ramificationIdx_mul' I this hw hw_bot).symm

theorem Ideal.IsDedekindDomain.finiteMulticity {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J : Ideal R} (hI : I ≠ ⊤) (hJ : J ≠ ⊥) :
    FiniteMultiplicity I J :=
  FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff]) hJ

open Pointwise in
@[simp]
theorem Ideal.smul_eq_bot_iff {M : Type*} {R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]
    {m : M} {I : Ideal R} : m • I = ⊥ ↔ I = ⊥ := by
  rw [smul_eq_iff_eq_inv_smul, smul_bot]

open Pointwise in
@[simp]
theorem Ideal.smul_top {M : Type*} {R : Type*} [Monoid M] [CommRing R] [MulSemiringAction M R] {m : M} :
    m • (⊤ : Ideal R) = ⊤ := by
  rw [← one_eq_top, smul_one]

open Pointwise in
@[simp]
theorem Ideal.smul_eq_top_iff {M : Type*} {R : Type*} [Group M] [CommRing R] [MulSemiringAction M R]
    {m : M} {I : Ideal R} : m • I = ⊤ ↔ I = ⊤ := by
  rw [smul_eq_iff_eq_inv_smul, smul_top]

open Pointwise in
theorem Ideal.smul_span {M : Type*} {R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]
    {m : M} {r : R} : m • span {r} = span {m • r} := by
  simp [pointwise_smul_def, map_span]
