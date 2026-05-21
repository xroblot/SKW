module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.GaussSum

@[expose] public section

open NumberField

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

theorem Ideal.absNorm_eq_card {S : Type*} [CommRing S] [Nontrivial S] [IsDedekindDomain S]
    [Module.Free ℤ S] (I : Ideal S) :
    Ideal.absNorm I = Nat.card (S ⧸ I) := rfl

theorem MulChar.ringHomComp_zpow {R : Type*} [CommMonoidWithZero R] {R' : Type*} [CommRing R'] {R'' : Type*}
    [CommRing R''] (χ : MulChar R R') (f : R' →+* R'') (n : ℤ) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [ringHomComp_pow]
  · simp [ringHomComp_pow, MulChar.ringHomComp_inv]

@[simps]
def MulChar.ringHomCompHom {R : Type*} [CommMonoid R] {R' : Type*} [CommRing R'] {R'' : Type*}
    [CommRing R''] (f : R' →+* R'') : MulChar R R' →* MulChar R R'' where
  toFun χ := MulChar.ringHomComp χ f
  map_one' := by rw [ringHomComp_one]
  map_mul' _ _ := MulChar.ringHomComp_mul _ _ f

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

noncomputable def AlgHom.equivFieldRange {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] (f : L →ₐ[K] L') :
    L ≃ₐ[K] f.fieldRange :=
  (AlgEquiv.ofBijective
    (f.codRestrict f.range fun x ↦ AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    ⟨fun _ _ h ↦ f.injective (congr_arg Subtype.val h),
     fun ⟨_, hy⟩ ↦ (AlgHom.mem_fieldRange.mp hy).imp fun _ hx => Subtype.ext hx⟩)

@[simp]
theorem equivFieldRange_apply {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] (f : L →ₐ[K] L') (x : L) : f.equivFieldRange x = f x :=
  rfl

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

theorem gaussSum_one_one {R : Type*} [CommRing R] [Fintype R] {R' : Type*}
    [CommRing R'] : gaussSum (1 : MulChar R R') (1 : AddChar R R') = Nat.card Rˣ := by
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]

theorem gaussSum_one_left {R : Type*} [Field R] [Fintype R] {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar R R'} (hψ : ψ ≠ 1) : gaussSum 1 ψ = -1 := by
  classical
  rw [gaussSum, ← Finset.univ.add_sum_erase _ (Finset.mem_univ 0), MulChar.map_zero, zero_mul,
    zero_add]
  have : ∀ x ∈ Finset.univ.erase (0 : R), (1 : MulChar R R') x = 1 :=
    fun x hx ↦ MulChar.one_apply <| isUnit_iff_ne_zero.mpr <| Finset.ne_of_mem_erase hx
  simp_rw +contextual [this, one_mul]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), AddChar.map_zero_eq_one, AddChar.sum_eq_ite,
    ite_sub, zero_sub, if_neg (by rwa [← AddChar.one_eq_zero])]

theorem gaussSum_one_right {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1) : gaussSum χ 1 = 0 := by
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ

theorem Ideal.multiplicity_bot {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ≠ ⊤) :
    multiplicity I ⊤ = 0 := by
  rw [← one_eq_top, multiplicity_of_one_right (by rwa [Ideal.isUnit_iff])]

theorem Ideal.emultiplicity_bot {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ≠ ⊤) :
    emultiplicity I ⊤ = 0 := by
  rw [← one_eq_top, emultiplicity_of_one_right (by rwa [Ideal.isUnit_iff])]

@[simp]
theorem MonoidHom.compAddChar_one {A M : Type*} [AddMonoid A] [Monoid M] {N : Type*}
    [Monoid N] (f : M →* N) :
    f.compAddChar (1 : AddChar A M) = 1 := by
  ext; simp

theorem MonoidHom.compAddChar_eq_one_iff {A M : Type*} [AddMonoid A] [Monoid M] {N : Type*}
    [Monoid N] {f : M →* N} (hf : Function.Injective f) {φ : AddChar A M} :
    f.compAddChar φ = 1 ↔ φ = 1 := by
  rw [← MonoidHom.compAddChar_one f, (f.compAddChar_injective_right hf).eq_iff]

theorem smul_eq_galRestrict_apply (A : Type*) {K L B : Type*} [CommRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [CommRing B] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] (σ : Gal(L/K)) (x : B) :
    σ • x = galRestrict A K L B σ x := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [algebraMap.smul', AlgEquiv.smul_def, algebraMap_galRestrict_apply]

@[simps]
def Ideal.mapEquiv {R S F : Type*} [CommSemiring R] [CommSemiring S] [EquivLike F R S]
    [RingHomClass F R S]  (e : F) : Ideal R ≃+* Ideal S where
  toFun := Ideal.map e
  invFun := Ideal.comap e
  __ := Ideal.mapHom e
  left_inv _ := by simpa using comap_map_of_bijective _ (EquivLike.bijective e)
  right_inv _ := by simpa using Ideal.map_comap_of_surjective _ (EquivLike.surjective e) _

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

theorem NumberField.Units.natAbs_norm (K : Type*) [Field K] [NumberField K] (x : (RingOfIntegers K)ˣ) :
    (Algebra.norm ℤ x.val).natAbs = 1 := by
  apply Rat.natCast_injective
  rw [Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int, NumberField.Units.norm, Nat.cast_one]

theorem NumberField.isUnit_iff_natAbs_norm {K : Type*} [Field K] [NumberField K] {x : RingOfIntegers K} :
    IsUnit x ↔ (Algebra.norm ℤ x).natAbs = 1 := by
  rw [isUnit_iff_norm, ← Rat.natCast_injective.eq_iff, RingOfIntegers.coe_norm,
    Nat.cast_natAbs, Nat.cast_one, ← Algebra.coe_norm_int, Int.cast_abs]

theorem MulChar.zpow_apply_coe_eq_apply_zpow {R : Type*} [CommGroupWithZero R] {R' : Type u_2}
    [CommMonoidWithZero R'] (χ : MulChar R R') (n : ℤ) (a : Rˣ) :
    (χ ^ n) a = χ (a ^ n : Rˣ) := by
  obtain ⟨n, (rfl | rfl)⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · rw [zpow_neg, zpow_natCast, inv_apply', ← Units.val_inv_eq_inv_val, pow_apply_coe, ← inv_zpow',
      zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

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

theorem Nat.digits_pow_sub_one {b : ℕ} (hb : 1 < b) (l : ℕ) :
    b.digits (b ^ l - 1) = List.replicate l (b - 1) := by
  suffices b ^ l - 1 = Nat.ofDigits b (List.replicate l (b - 1)) by
    rw [this, Nat.digits_ofDigits _ hb _ (by grind) (by grind)]
  induction l with
    | zero => simp
    | succ l hl =>
        rw [List.replicate_succ, Nat.ofDigits_cons, ← hl, add_comm (b - 1), Nat.mul_sub, mul_one,
          ← Nat.pow_succ', ← Nat.add_sub_assoc hb.le,
          Nat.sub_add_cancel (Nat.le_self_pow l.succ_ne_zero b)]

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

@[to_additive]
theorem Finset.prod_filter_eq_eq_pow_card {α β γ : Type*} [Fintype α] [CommMonoid γ]
    [DecidableEq β] (f : α → β) (b : β) (g : β → γ) :
    ∏ x with b = f x, g (f x) = g b ^ Fintype.card {x // b = f x} := by
  rw [Finset.pow_eq_prod_const, Finset.prod_range,
    Finset.prod_subtype (p := fun x ↦ b = f x) _ (by simp)]
  exact Fintype.prod_equiv (Fintype.equivFin _) _ _ fun x ↦ by rw [← x.prop]

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst {α β : Type*} [Group α]
    [MulAction α β] (b : β) (a : α) :
    ((MulAction.orbitProdStabilizerEquivGroup α b).symm a).1 = a • b := rfl

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_apply_smul {α β : Type*} [Group α]
    [MulAction α β] (b : β) (x : orbit α b) (y : stabilizer α b) :
    MulAction.orbitProdStabilizerEquivGroup α b (x, y) • b = x := by
  rw [← MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst, Equiv.symm_apply_apply]

-- @[to_additive]
-- noncomputable def MulAction.ofOrbit {α β : Type*} [Group α] [MulAction α β] {b : β}
--     (x : orbit α b) : α := x.prop.choose

-- @[to_additive (attr := simp)]
-- theorem MulAction.ofOrbit_smul {α β : Type*} [Group α] [MulAction α β] {b : β}
--     (x : orbit α b) : ofOrbit x • b = x := x.prop.choose_spec

-- @[to_additive (attr := simp)]
-- theorem MulAction.orbitEquivQuotientStabilizer_apply {α β : Type*} [Group α] [MulAction α β]
--     {b : β} (x : orbit α b) :
--     orbitEquivQuotientStabilizer α b x = ofOrbit x := by
--   simp [orbitEquivQuotientStabilizer, Equiv.symm_apply_eq]

-- @[to_additive (attr := simp)]
-- theorem MulAction.orbitProdStabilizerEquivGroup_apply {α β : Type*} [Group α] [MulAction α β]
--     (b : β) (a : α) (x : orbit α b) (σ : stabilizer α b) :
--     orbitProdStabilizerEquivGroup α b (x, σ) = ofOrbit x * σ := by
--   rw [orbitProdStabilizerEquivGroup]
--   simp
