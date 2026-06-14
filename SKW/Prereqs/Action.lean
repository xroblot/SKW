module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.SMulWithZero

@[expose] public section

variable {G M : Type*} [Group G] [MonoidWithZero M]
  [MulDistribMulAction G M] [SMulZeroClass G M]

theorem smul_mem_nonZeroDivisorsLeft (g : G) {m : M} (hm : m ∈ nonZeroDivisorsLeft M) :
    g • m ∈ nonZeroDivisorsLeft M := fun y hy => by
  have h : m * (g⁻¹ • y) = 0 := by
    have := congr_arg (g⁻¹ • ·) hy
    rwa [smul_zero, smul_mul', inv_smul_smul] at this
  have h0 := hm _ h
  calc y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
    _ = g • (0 : M) := by rw [h0]
    _ = 0 := smul_zero g

theorem smul_mem_nonZeroDivisorsRight (g : G) {m : M} (hm : m ∈ nonZeroDivisorsRight M) :
    g • m ∈ nonZeroDivisorsRight M := fun y hy => by
  have h : (g⁻¹ • y) * m = 0 := by
    have := congr_arg (g⁻¹ • ·) hy
    rwa [smul_zero, smul_mul', inv_smul_smul] at this
  have h0 := hm _ h
  calc y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
    _ = g • (0 : M) := by rw [h0]
    _ = 0 := smul_zero g

theorem smul_mem_nonZeroDivisors (g : G) {m : M} (hm : m ∈ nonZeroDivisors M) :
    g • m ∈ nonZeroDivisors M :=
  mem_nonZeroDivisors_iff'.mpr
    ⟨smul_mem_nonZeroDivisorsLeft g hm.1, smul_mem_nonZeroDivisorsRight g hm.2⟩

instance : SMul G (nonZeroDivisors M) where
  smul g m := ⟨g • m, smul_mem_nonZeroDivisors g m.prop⟩

@[simp]
theorem nonZeroDivisors.val_smul (g : G) (m : nonZeroDivisors M) :
    (g • m : nonZeroDivisors M).val = g • m.val := rfl

instance : MulAction G (nonZeroDivisors M) where
  one_smul m := Subtype.val_injective (by simp)
  mul_smul g h m := Subtype.val_injective (by simp [mul_smul])

instance : MulDistribMulAction G (nonZeroDivisors M) where
  smul_one g := Subtype.val_injective (by simp)
  smul_mul g m n := Subtype.val_injective (by simp [smul_mul'])

end
