module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Galois

public import SKW.PRed2Mathlib.NumberTheory

@[expose] public section

open NumberField

/-! ### NumberField -/

theorem NumberField.exists_integer_multiple {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ (d : ℤ), d ≠ 0 ∧ d * x ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨⟨_, ⟨b, hb, rfl⟩⟩, hb'⟩ :=
    IsLocalization.exists_integer_multiple (Algebra.algebraMapSubmonoid (𝓞 K) (nonZeroDivisors ℤ)) x
  exact ⟨b, nonZeroDivisors.ne_zero hb, hb'⟩

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

/-! ### ArithmeticFunction.phi -/

def ArithmeticFunction.phi : ArithmeticFunction ℤ where
  toFun n := Nat.totient n
  map_zero' := by simp

@[simp]
theorem ArithmeticFunction.phi_apply (n : ℕ) :
    phi n = Nat.totient n := rfl

open Nat in
theorem ArithmeticFunction.isMultiplicative_phi :
    IsMultiplicative phi :=
  IsMultiplicative.iff_ne_zero.mpr ⟨by simp, fun _ _ h ↦ by simp [Nat.totient_mul h]⟩

theorem Nat.totient_mul_totient_eq (m n : ℕ) :
    totient m * totient n = totient (lcm m n) * totient (gcd m n) := by
  have :=  ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply
    ArithmeticFunction.isMultiplicative_phi (x := m) (y := n)
  rwa [ArithmeticFunction.phi_apply, ArithmeticFunction.phi_apply, ArithmeticFunction.phi_apply,
    ArithmeticFunction.phi_apply, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_inj, eq_comm] at this
