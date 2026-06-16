module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import SKW.Prereqs.FractionalIdeal

open scoped nonZeroDivisors Pointwise

@[expose] public section

/-!
# Action of a group on the class group

A `MulSemiringAction G R` on a Dedekind domain `R` induces a `MulDistribMulAction G (ClassGroup R)`.

The action is defined on the natural model of the class group as a quotient of the units of
fractional ideals: `g` acts through the `G`-action on `FractionalIdeal R⁰ (FractionRing R)` (see
`SKW.Prereqs.FractionalIdeal`), which preserves the principal ideals and so descends to the
quotient. With this definition `g • [u] = [g • u]` holds essentially definitionally
(`ClassGroup.smul_mk`), and the integral-ideal version `g • [I] = [g • I]`
(`ClassGroup.smul_mk0`) follows.
-/

namespace ClassGroup

open FractionalIdeal

variable {G R : Type*} [Group G] [CommRing R] [IsDedekindDomain R] [MulSemiringAction G R]

attribute [local instance] Units.mulDistribMulActionRight

/-- The `G`-action on fractional ideals preserves the principal ideals. -/
theorem principalIdeals_le_comap (g : G) :
    (toPrincipalIdeal R (FractionRing R)).range ≤
      (toPrincipalIdeal R (FractionRing R)).range.comap
        (MulDistribMulAction.toMulAut G (FractionalIdeal R⁰ (FractionRing R))ˣ g).toMonoidHom := by
  intro I hI
  rw [mem_principal_ideals_iff] at hI
  obtain ⟨x, hx⟩ := hI
  rw [Subgroup.mem_comap, mem_principal_ideals_iff]
  exact ⟨g • x, by rw [← spanSingleton_smul, hx]; rfl⟩

/-- The action of `g` on the class group, as a group homomorphism: descend the pointwise action
on the units of fractional ideals along the quotient by principal ideals. -/
noncomputable def mapAut (g : G) : ClassGroup R →* ClassGroup R :=
  QuotientGroup.map (toPrincipalIdeal R (FractionRing R)).range
    (toPrincipalIdeal R (FractionRing R)).range
    (MulDistribMulAction.toMulAut G _ g).toMonoidHom (principalIdeals_le_comap g)

noncomputable instance instSMul : SMul G (ClassGroup R) where
  smul g := mapAut g

@[simp]
theorem smul_mk (g : G) (u : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    g • ClassGroup.mk (FractionRing R) u = ClassGroup.mk (FractionRing R) (g • u) := by
  rw [← Quot_mk_eq_mk, ← Quot_mk_eq_mk]
  rfl

@[simp]
theorem smul_mk0 (g : G) (I : (Ideal R)⁰) : g • mk0 I = mk0 (g • I) := by
  rw [← mk_mk0 (K := FractionRing R), smul_mk, ← mk_mk0 (K := FractionRing R)]
  congr 1
  ext1
  rw [Units.coe_smul, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
    nonZeroDivisors.val_smul, coeIdeal_smul]

noncomputable instance instMulDistribMulAction : MulDistribMulAction G (ClassGroup R) where
  one_smul c := by obtain ⟨I, rfl⟩ := mk0_surjective c; rw [smul_mk0, one_smul]
  mul_smul g h c := by
    obtain ⟨I, rfl⟩ := mk0_surjective c; rw [smul_mk0, smul_mk0, smul_mk0, mul_smul]
  smul_one g := map_one (mapAut g)
  smul_mul g c d := map_mul (mapAut g) c d

-- The `MulDistribMulAction` reuses `instSMul` (no parallel `SMul` instance / diamond).
example (g : G) (c : ClassGroup R) : g • c = mapAut g c := by
  with_reducible_and_instances rfl

end ClassGroup

end
