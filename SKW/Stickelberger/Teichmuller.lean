/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

-- for `MulEquiv.ofBijective_symm_apply_apply`, the `MulEquiv` half of a pair Mathlib only has
-- for `Equiv`; too small for a PR of its own, so it ships with this file.
public import SKW.Prereqs.AlgebraMisc

-- for `rootsOfUnity.mapQuot` and `rootsOfUnity.coe_mapQuot`, submitted upstream as #44588,
-- which generalizes `Ideal.rootsOfUnityMapQuot`; this import goes once that merges.
public import SKW.PRed2Mathlib.Teichmuller

/-!
# The Teichmüller character

Let `I` be an ideal of a ring `R` such that reduction modulo `I` is a bijection from the roots of
unity of `R` of order `n` onto the units of `R ⧸ I`. Inverting it and extending by zero gives a
multiplicative character of `R ⧸ I` with values in `R`, the Teichmüller character, which is a
multiplicative section of the reduction map.

## Main definitions

* `MulChar.teichmuller`: the Teichmüller character of `R ⧸ I`, with values in `R`.

## Main results

* `MulChar.mk_teichmuller_apply`: for a maximal ideal `I`, the Teichmüller character is a section
  of the reduction map.
* `MulChar.orderOf_teichmuller`: the Teichmüller character has order `n`.
* `MulChar.exists_nat_teichmuller_zpow_eq_pow`: over a domain containing a primitive `n`-th root
  of unity `ζ`, the values of the powers of the Teichmüller character at units are powers of `ζ`.
* `MulChar.map_ringHomComp_teichmuller_zpow_apply`: a map sending `f ζ` to `(f ζ) ^ m` multiplies
  by `m` the exponent of a power of the Teichmüller character composed with `f`.

## Tags

Teichmüller character, multiplicative character, roots of unity

-/

public section

variable {R : Type*} [CommRing R] {n : ℕ} {I : Ideal R}
  (hbij : Function.Bijective (rootsOfUnity.mapQuot n I))

namespace MulChar

/-- The Teichmüller character of `R ⧸ I`: the multiplicative character with values in `R`
obtained by inverting the reduction of the roots of unity of order `n` and extending by zero. -/
noncomputable def teichmuller : MulChar (R ⧸ I) R :=
  MulChar.ofUnitHom <| (rootsOfUnity n R).subtype.comp
    (MulEquiv.ofBijective _ hbij).symm.toMonoidHom

/-- The value of the Teichmüller character at a unit. -/
@[simp]
theorem teichmuller_apply_coe (x : (R ⧸ I)ˣ) :
    teichmuller hbij x = ((MulEquiv.ofBijective _ hbij).symm x : Rˣ) := by
  simp [teichmuller]

attribute [local instance] Ideal.Quotient.field in
/-- The Teichmüller character is a section of the reduction map `R → R ⧸ I`. -/
@[simp]
theorem mk_teichmuller_apply [I.IsMaximal] (x : R ⧸ I) :
    Ideal.Quotient.mk I (teichmuller hbij x) = x := by
  obtain rfl | ⟨u, rfl⟩ := GroupWithZero.eq_zero_or_unit x
  · simp
  · simp [← rootsOfUnity.coe_mapQuot]

/-- The `n`-th power of the Teichmüller character is trivial. -/
theorem teichmuller_pow_eq_one : teichmuller hbij ^ n = 1 := by
  ext
  simp [teichmuller, MulChar.pow_apply_coe, ← mem_rootsOfUnity']

/-- A power of the Teichmüller character whose exponent is divisible by `n` is trivial. -/
theorem teichmuller_zpow_eq_one_of_dvd {a : ℤ} (ha : (n : ℤ) ∣ a) : teichmuller hbij ^ a = 1 := by
  obtain ⟨c, rfl⟩ := ha
  rw [zpow_mul, zpow_natCast, teichmuller_pow_eq_one, one_zpow]

/-- The Teichmüller character has order `n`. -/
theorem orderOf_teichmuller [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    orderOf (teichmuller hbij) = n := by
  refine (orderOf_eq_iff (NeZero.pos _)).mpr ⟨teichmuller_pow_eq_one hbij,
    fun m hmn hm ↦ MulChar.ne_one_iff.mpr ⟨rootsOfUnity.mapQuot n I hζ.toRootsOfUnity, ?_⟩⟩
  rw [teichmuller, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.ofBijective_symm_apply_apply, Subgroup.subtype_apply,
    IsPrimitiveRoot.val_toRootsOfUnity_coe, ne_eq, hζ.pow_eq_one_iff_dvd]
  exact Nat.not_dvd_of_pos_of_lt hm hmn

/-- The Teichmüller character is nontrivial as soon as `n ≠ 1`. -/
theorem teichmuller_ne_one [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 1) :
    teichmuller hbij ≠ 1 :=
  orderOf_eq_one_iff.not.mp <| by rwa [orderOf_teichmuller hbij hζ]

/-- A power of the Teichmüller character is trivial exactly when `n` divides its exponent. -/
theorem teichmuller_zpow_eq_one_iff [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) {a : ℤ} :
    teichmuller hbij ^ a = 1 ↔ (n : ℤ) ∣ a := by
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_teichmuller hbij hζ]

/-- The order of a power of the Teichmüller character divides `n`. -/
theorem orderOf_teichmuller_zpow_dvd (a : ℤ) : orderOf (teichmuller hbij ^ a) ∣ n :=
  (orderOf_dvd_of_mem_zpowers <| Subgroup.zpow_mem_zpowers (teichmuller hbij) a).trans
    (orderOf_dvd_of_pow_eq_one (teichmuller_pow_eq_one hbij))

/-- The values at units of the powers of the Teichmüller character are powers of `ζ`. -/
theorem exists_nat_teichmuller_zpow_eq_pow [IsDomain R] [NeZero n] {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) (a : ℤ) (x : (R ⧸ I)ˣ) :
    ∃ m : ℕ, (teichmuller hbij ^ a) x = ζ ^ m := by
  suffices ((teichmuller hbij ^ a) x) ^ n = 1 by
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one this
    exact ⟨a, ha.symm⟩
  simpa [← MulChar.pow_apply_coe] using DFunLike.congr_fun
    (orderOf_dvd_iff_pow_eq_one.mp (orderOf_teichmuller_zpow_dvd hbij a)) x.val

/-- A ring homomorphism sending `ζ` to `ζ ^ m` multiplies by `m` the exponent of a power of the
Teichmüller character. -/
theorem map_ringHomComp_teichmuller_zpow_apply [IsDomain R] [NeZero n] {S : Type*}
    [CommRing S] {F : Type*} [FunLike F S S] [MonoidWithZeroHomClass F S S] (σ : F) (f : R →+* S)
    (m : ℕ) {ζ : R} (hζ : IsPrimitiveRoot ζ n) (hσ : σ (f ζ) = (f ζ) ^ m) (a : ℤ)
    (x : R ⧸ I) :
    σ ((teichmuller hbij ^ a).ringHomComp f x) = (teichmuller hbij ^ (a * m)).ringHomComp f x := by
  by_cases hx : IsUnit x
  · lift x to (R ⧸ I)ˣ using hx
    obtain ⟨t, ht⟩ := exists_nat_teichmuller_zpow_eq_pow hbij hζ a x
    rw [MulChar.ringHomComp_apply, ht, map_pow, map_pow, hσ, MulChar.ringHomComp_apply,
      zpow_mul, zpow_natCast, MulChar.pow_apply_coe, ht, map_pow, map_pow, pow_right_comm]
  · simp [MulChar.map_nonunit _ hx]

end MulChar
