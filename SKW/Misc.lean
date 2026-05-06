module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification

@[expose] public section

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
  cases n with
  | ofNat _ => simp [ringHomComp_pow]
  | negSucc m => simp [zpow_negSucc, ringHomComp_pow, MulChar.ringHomComp_inv]

@[simps]
def MulChar.ringHomCompHom {R : Type*} [CommMonoid R] {R' : Type*} [CommRing R'] {R'' : Type*}
    [CommRing R''] (f : R' →+* R'') : MulChar R R' →* MulChar R R'' where
  toFun χ := MulChar.ringHomComp χ f
  map_one' := by rw [ringHomComp_one]
  map_mul' _ _ := MulChar.ringHomComp_mul _ _ f

theorem NumberField.isUnit_iff_norm' {K : Type*} [Field K] [NumberField K] {x : RingOfIntegers K} :
    IsUnit x ↔ (Algebra.norm ℤ x).natAbs = 1 := by
  rw [isUnit_iff_norm, ← (FaithfulSMul.algebraMap_injective ℕ ℚ).eq_iff, RingOfIntegers.coe_norm,
    eq_natCast, Nat.cast_natAbs, map_one, ← Algebra.coe_norm_int, Int.cast_abs]

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

