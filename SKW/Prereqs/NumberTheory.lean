module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Galois

public import SKW.Prereqs.Stickelberger


set_option linter.style.header false

@[expose] public section

open NumberField

/-! ### NumberField -/

theorem NumberField.exists_integer_multiple {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ (d : ℤ), d ≠ 0 ∧ d * x ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨⟨_, ⟨b, hb, rfl⟩⟩, hb'⟩ :=
    IsLocalization.exists_integer_multiple (Algebra.algebraMapSubmonoid (𝓞 K) (nonZeroDivisors ℤ)) x
  exact ⟨b, nonZeroDivisors.ne_zero hb, hb'⟩

theorem NumberField.Units.natAbs_norm (K : Type*) [Field K] [NumberField K] (x : (RingOfIntegers
  K)ˣ) :
    (Algebra.norm ℤ x.val).natAbs = 1 := by
  apply Rat.natCast_injective
  rw [Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int, NumberField.Units.norm, Nat.cast_one]

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
theorem NumberField.isUnit_iff_natAbs_norm {K : Type*} [Field K] [NumberField K] {x :
  RingOfIntegers K} :
    IsUnit x ↔ (Algebra.norm ℤ x).natAbs = 1 := by
  rw [isUnit_iff_norm, ← Rat.natCast_injective.eq_iff, RingOfIntegers.coe_norm,
    Nat.cast_natAbs, Nat.cast_one, ← Algebra.coe_norm_int, Int.cast_abs]
-/

/-! ### Galois / galRestrict -/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
theorem smul_eq_galRestrict_apply (A : Type*) {K L B : Type*} [CommRing A] [Field K] [Field L]
    [CommRing B] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] (σ : Gal(L/K)) (x : B) :
    σ • x = galRestrict A K L B σ x := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [algebraMap.smul', AlgEquiv.smul_def, algebraMap_galRestrict_apply]
-/

/-! ### ZMod -/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
-- TODO(SKW): upstream, next to `ZMod.ringHom_map_cast` in `Mathlib/Data/ZMod/Basic.lean`, which
-- is the statement for a ring homomorphism into `ZMod n`, probably with `@[simp]` like it.
/-- A ring homomorphism commutes with the cast from `ZMod n`. -/
theorem ZMod.map_cast {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (k : ZMod n) :
    f (ZMod.cast k) = ZMod.cast k := by
  cases n
  · exact map_intCast f k
  · exact map_natCast f k.val
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
-- TODO(SKW): no obvious home in Mathlib, `Mathlib/RingTheory/Trace/Basic.lean`, next to
-- `Algebra.trace_eq_of_equiv_equiv`, knowing nothing about `ZMod`.
/-- The trace does not care whether the base ring is `ZMod p` or a ring isomorphic to it. -/
theorem ZMod.cast_trace_eq_trace {p : ℕ} {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [Algebra (ZMod p) C] (e : A ≃+* ZMod p) (x : C) :
    ZMod.cast (Algebra.trace (ZMod p) C x) = Algebra.trace A C x := by
  have : Subsingleton (A →+* C) := ⟨fun f g ↦ RingHom.ext fun y ↦ by
    obtain ⟨z, rfl⟩ := e.symm.surjective y
    exact congr($(Subsingleton.elim (f.comp (e.symm : ZMod p →+* A)) (g.comp e.symm)) z)⟩
  rw [Algebra.trace_eq_of_equiv_equiv e (RingEquiv.refl C) (Subsingleton.elim _ _) x]
  exact e.eq_symm_apply.mpr (ZMod.ringHom_map_cast (e : A →+* ZMod p) _)
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
-- TODO(SKW): upstream, next to `Nat.pow_sub_one_mod_pow_sub_one` in
-- `Mathlib/Data/Nat/GCD/Basic.lean`.
/-- For `1 < a`, the number `a ^ m - 1` divides `a ^ n - 1` precisely when `m` divides `n`. -/
theorem Nat.pow_sub_one_dvd_pow_sub_one_iff {a : ℕ} (ha : 1 < a) {n m : ℕ} :
    a ^ m - 1 ∣ a ^ n - 1 ↔ m ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.pow_sub_one_mod_pow_sub_one, Nat.sub_eq_zero_iff_le,
    ← pow_zero a, Nat.pow_le_pow_iff_right ha, Nat.le_zero, Nat.dvd_iff_mod_eq_zero]
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
theorem ZMod.orderOf_mod_self_pow_sub_one (a k : ℕ) (ha : 1 < a) :
    orderOf (a : ZMod (a ^ k - 1)) = k := by
  have key (n : ℕ) : (a : ZMod (a ^ k - 1)) ^ n = 1 ↔ k ∣ n := by
    rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod (a ^ k - 1)), ZMod.natCast_eq_natCast_iff,
      Nat.ModEq.comm, Nat.modEq_iff_dvd, ← Nat.cast_sub (Nat.one_le_pow _ _ (by lia : 0 < a)),
      Int.natCast_dvd_natCast, Nat.pow_sub_one_dvd_pow_sub_one_iff ha]
  exact Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr ((key k).mpr dvd_rfl))
    ((key _).mp (pow_orderOf_eq_one _))
-/

/-! ### ArithmeticFunction.phi -/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
def ArithmeticFunction.phi : ArithmeticFunction ℤ where
  toFun n := Nat.totient n
  map_zero' := by simp
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
@[simp]
theorem ArithmeticFunction.phi_apply (n : ℕ) :
    phi n = Nat.totient n := rfl
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
open Nat in
theorem ArithmeticFunction.isMultiplicative_phi :
    IsMultiplicative phi :=
  IsMultiplicative.iff_ne_zero.mpr ⟨by simp, fun _ _ h ↦ by simp [Nat.totient_mul h]⟩
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
theorem Nat.totient_mul_totient_eq (m n : ℕ) :
    totient m * totient n = totient (lcm m n) * totient (gcd m n) := by
  have :=  ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply
    ArithmeticFunction.isMultiplicative_phi (x := m) (y := n)
  rwa [ArithmeticFunction.phi_apply, ArithmeticFunction.phi_apply, ArithmeticFunction.phi_apply,
    ArithmeticFunction.phi_apply, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_inj, eq_comm] at this
-/

/-! ### FiniteField -/

namespace FiniteField

open Finset

variable (K : Type*) [Field K] [Fintype K]

local notation "q" => Fintype.card K

-- TODO(SKW): upstream `sum_sdiff_zero`, `sum_pow` and `sum_univ_id_eq_ite` into
-- `Mathlib/FieldTheory/Finite/Basic.lean`, right after `FiniteField.sum_pow_units`; the proof of
-- `sum_pow_lt_card_sub_one'` below then replaces the one of
-- `FiniteField.sum_pow_lt_card_sub_one`, whose name it takes over there.
-- Copied to `SKW.Prereqs.Stickelberger`.
/-
/-- A sum over the nonzero elements of a finite field is a sum over its units. -/
theorem sum_sdiff_zero {M : Type*} [AddCommMonoid M] [DecidableEq K] (f : K → M) :
    ∑ x ∈ univ \ {0}, f x = ∑ x : Kˣ, f x := by
  let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
  have : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  simp [← this, univ.sum_map φ, φ]
-/

/-- The sum of `x ^ i`, with `i ≠ 0`, as `x` ranges over a finite field of cardinality `q`
is equal to `-1` if `q - 1 ∣ i`, and to `0` otherwise. -/
theorem sum_pow (i : ℕ) (hi : i ≠ 0) :
    ∑ x : K, x ^ i = if q - 1 ∣ i then -1 else 0 := by
  classical
  rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hi, add_zero,
    sum_sdiff_zero, sum_pow_units K i]

/-- The sum of all the elements of a finite field of cardinality `q` is equal to `1` if `q = 2`,
and to `0` otherwise. -/
theorem sum_univ_id_eq_ite :
    ∑ x : K, x = if q = 2 then 1 else 0 := by
  rw [show ∑ x : K, x = ∑ x : K, x ^ 1 by simp, sum_pow K 1 one_ne_zero]
  simp only [Nat.dvd_one, Nat.pred_eq_succ_iff, zero_add]
  split_ifs with hq
  · rw [neg_eq_iff_add_eq_zero]
    exact_mod_cast hq ▸ cast_card_eq_zero K
  · rfl

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
/-- The sum of `x⁻¹ * x ^ (i + 1)` as `x` ranges over a finite field of cardinality `q` is equal
to `-1` if `q - 1 ∣ i`, and to `0` otherwise. -/
theorem sum_inv_mul_pow_succ (i : ℕ) :
    ∑ x : K, x⁻¹ * x ^ (i + 1) = if q - 1 ∣ i then -1 else 0 := by
  classical
  rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, inv_zero, zero_mul, add_zero,
    sum_congr rfl (g := (· ^ i)), sum_sdiff_zero, sum_pow_units K i]
  grind
-/

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
theorem sum_pow_lt_card_sub_one' (i : ℕ) (h : i < q - 1) : ∑ x : K, x ^ i = 0 := by
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [sum_pow K _ hi, ite_eq_right]
  contrapose! h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h

end FiniteField
