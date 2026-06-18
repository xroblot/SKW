module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.GaussSum

/-!
# PRed to Mathlib: Gauss sums of trivial characters

The declarations in this file were extracted from `SKW.Prereqs.MulChars` and submitted
upstream as Mathlib PR [#40730](https://github.com/leanprover-community/mathlib4/pull/40730).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.MulChars`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

@[expose] public section

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

end
