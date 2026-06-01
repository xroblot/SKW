module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.FieldTheory.LinearDisjoint

public import SKW.Prereqs.AlgebraMisc

@[expose] public section

open NumberField

/-! ### Ideal -/

theorem Ideal.absNorm_eq_card {S : Type*} [CommRing S] [Nontrivial S] [IsDedekindDomain S]
    [Module.Free ℤ S] (I : Ideal S) :
    Ideal.absNorm I = Nat.card (S ⧸ I) := rfl

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

theorem Ideal.liesOver_of_absNorm_dvd_prime_pow {R : Type*} [CommRing R] [Nontrivial R]
    [IsDedekindDomain R] [Module.Free ℤ R] [Algebra.IsIntegral ℤ R] (I : Ideal R)
    [I.IsPrime] {p k : ℕ} [hp : Fact (Nat.Prime p)] (hI : Ideal.absNorm I ∣ p ^ k) :
    I.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : NeZero I := ⟨by
    contrapose! hI
    rw [hI, map_zero, Nat.zero_dvd]
    exact NeZero.ne (p ^ k)⟩
  have := (Int.absNorm_under_dvd_absNorm I).trans hI
  rw [Ideal.liesOver_iff, ← Nat.prime_eq_prime_of_dvd_pow (Nat.absNorm_under_prime I)
    hp.out this, Int.ideal_span_absNorm_eq_self]

/-! ### Ideal — IsDedekindDomain / emultiplicity -/

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

/-! ### IsCyclotomicExtension -/

open NumberField in
theorem IsCyclotomicExtension.Rat.discr_coprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (K₁ K₂ : Type*)
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂] [IsCyclotomicExtension {n₁} ℚ K₁]
    [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
  rw [Int.isCoprime_iff_nat_coprime, natAbs_discr  n₁ K₁, natAbs_discr  n₂ K₂]
  refine Nat.Coprime.coprime_div_left ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
  refine Nat.Coprime.coprime_div_right ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
  exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ h)

theorem IntermediateField.linearDisjoint_iff'' {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : IntermediateField F E) (L : Type*) [Field L] [Algebra F L] [Algebra L E]
    [IsScalarTower F L E] :
    A.LinearDisjoint L ↔ A.LinearDisjoint (IsScalarTower.toAlgHom F L E).fieldRange := by
  rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]

theorem IsCyclotomicExtension.Rat.linearDisjoint_ofCoprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    {E : Type*} [Field E] [NumberField E] (K₁ : IntermediateField ℚ E) [NumberField K₁] (K₂ : Type*)
    [Field K₂] [NumberField K₂] [Algebra K₂ E] [IsCyclotomicExtension {n₁} ℚ K₁]
    [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    K₁.LinearDisjoint K₂ := by
  have : IsCyclotomicExtension {n₂} ℚ (IsScalarTower.toAlgHom ℚ K₂ E).fieldRange :=
    .equiv _ ℚ K₂ (AlgHom.equivFieldRange _)
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois {n₁} ℚ K₁
  rw [IntermediateField.linearDisjoint_iff'']
  exact NumberField.linearDisjoint_of_isGalois_isCoprime_discr E _ _ <| discr_coprime n₁ n₂ K₁ _ h
