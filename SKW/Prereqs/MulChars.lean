module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.GaussSum

@[expose] public section

/-! ### MulChar -/

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

theorem MulChar.zpow_apply_coe_eq_apply_zpow {R : Type*} [CommGroupWithZero R] {R' : Type u_2}
    [CommMonoidWithZero R'] (χ : MulChar R R') (n : ℤ) (a : Rˣ) :
    (χ ^ n) a = χ (a ^ n : Rˣ) := by
  obtain ⟨n, (rfl | rfl)⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · rw [zpow_neg, zpow_natCast, inv_apply', ← Units.val_inv_eq_inv_val, pow_apply_coe, ← inv_zpow',
      zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

/-! ### AddChar / MonoidHom.compAddChar -/

@[simp]
theorem MonoidHom.compAddChar_one {A M : Type*} [AddMonoid A] [Monoid M] {N : Type*}
    [Monoid N] (f : M →* N) :
    f.compAddChar (1 : AddChar A M) = 1 := by
  ext; simp

theorem MonoidHom.compAddChar_eq_one_iff {A M : Type*} [AddMonoid A] [Monoid M] {N : Type*}
    [Monoid N] {f : M →* N} (hf : Function.Injective f) {φ : AddChar A M} :
    f.compAddChar φ = 1 ↔ φ = 1 := by
  rw [← MonoidHom.compAddChar_one f, (f.compAddChar_injective_right hf).eq_iff]

/-! ### Gauss sums -/

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
