module

public import SKW.PRed2Mathlib.FractionalIdeal
public import SKW.PRed2Mathlib.Action
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
# Action of a group on fractional ideals

Given a group `G` acting on a commutative ring `R` and on an `R`-algebra `P` by ring
automorphisms, compatibly via `SMulDistribClass G R P` (i.e. `algebraMap R P` is `G`-equivariant,
`g • (r • x) = (g • r) • (g • x)`) and keeping the submonoid `S` invariant (`hS`), the action of
`G` on `P` carries each fractional ideal `I : FractionalIdeal S P` to a fractional ideal. This
produces a `MulDistribMulAction G (FractionalIdeal S P)` (`FractionalIdeal.mulDistribMulAction`).

The compatibility is exactly `SMulDistribClass G R P`, whose `smul_distrib_smul` field is the
semilinearity law and which makes `algebraMap.smul'` (`algebraMap R P (g • r) = g • algebraMap R P r`)
available. For a tower of Galois extensions this class holds as an instance, so no compatibility
argument is needed at the call site.
-/

namespace FractionalIdeal

section General

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]
  {G : Type*} [Group G] [MulSemiringAction G R] [MulSemiringAction G P] [SMulDistribClass G R P]

/-- The image of a submodule `N ⊆ P` under the ring automorphism induced by `g`. -/
def smulSubmodule (g : G) (N : Submodule R P) : Submodule R P where
  carrier := (g • · : P → P) '' N
  add_mem' := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a + b, N.add_mem ha hb, smul_add g a b⟩
  zero_mem' := ⟨0, N.zero_mem, smul_zero g⟩
  smul_mem' c y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨(g⁻¹ • c) • x, N.smul_mem _ hx, ?_⟩
    show g • ((g⁻¹ • c) • x) = c • (g • x)
    rw [smul_distrib_smul, smul_inv_smul]

theorem mem_smulSubmodule {g : G} {N : Submodule R P} {y : P} :
    y ∈ smulSubmodule g N ↔ ∃ x ∈ N, g • x = y := Set.mem_image _ _ _

/-- Equivariance of the algebra map (a restatement of `algebraMap.smul'` with the types
spelled out, so it can be used without instance metavariables). -/
theorem algebraMap_smul (g : G) (r : R) :
    algebraMap R P (g • r) = g • algebraMap R P r := algebraMap.smul' g r P

variable (hS : ∀ (g : G) {s : R}, s ∈ S → g • s ∈ S)

include hS

/-- The image of a fractional ideal under the ring automorphism induced by `g`. -/
def smulFractional (g : G) (I : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨smulSubmodule g (I : Submodule R P), by
    obtain ⟨a, ha, H⟩ := I.isFractional
    refine ⟨g • a, hS g ha, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := H x hx
    exact ⟨g • r, by rw [← smul_distrib_smul, ← hr, algebraMap_smul]⟩⟩

theorem coe_smulFractional (g : G) (I : FractionalIdeal S P) :
    (↑(smulFractional hS g I) : Submodule R P) = smulSubmodule g (I : Submodule R P) :=
  rfl

theorem mem_smulFractional {g : G} {I : FractionalIdeal S P} {y : P} :
    y ∈ smulFractional hS g I ↔ ∃ x ∈ I, g • x = y := mem_smulSubmodule

theorem smulFractional_one (I : FractionalIdeal S P) : smulFractional hS 1 I = I :=
  coeToSubmodule_injective <| Submodule.ext fun y => by
    simp [coe_smulFractional, mem_smulSubmodule]

theorem smulFractional_mul (g h : G) (I : FractionalIdeal S P) :
    smulFractional hS (g * h) I
      = smulFractional hS g (smulFractional hS h I) :=
  coeToSubmodule_injective <| Submodule.ext fun y => by
    simp only [coe_smulFractional, mem_smulSubmodule]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨h • x, ⟨x, hx, rfl⟩, (mul_smul g h x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, mul_smul g h x⟩

theorem smulFractional_smul_one (g : G) : smulFractional hS g (1 : FractionalIdeal S P) = 1 :=
  coeToSubmodule_injective <| Submodule.ext fun y => by
    simp only [coe_smulFractional, coe_one, mem_smulSubmodule, Submodule.mem_one]
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩; exact ⟨g • r, algebraMap_smul g r⟩
    · rintro ⟨r, rfl⟩
      exact ⟨algebraMap R P (g⁻¹ • r), ⟨g⁻¹ • r, rfl⟩, by rw [← algebraMap_smul, smul_inv_smul]⟩

theorem smulFractional_smul_mul (g : G) (I J : FractionalIdeal S P) :
    smulFractional hS g (I * J)
      = smulFractional hS g I * smulFractional hS g J :=
  coeToSubmodule_injective <| by
    simp only [coe_smulFractional, coe_mul]
    refine le_antisymm ?_ (Submodule.mul_le.mpr ?_)
    · intro y hy
      rw [mem_smulSubmodule] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro a ha b hb
        rw [smul_mul']
        exact Submodule.mul_mem_mul (mem_smulSubmodule.mpr ⟨a, ha, rfl⟩)
          (mem_smulSubmodule.mpr ⟨b, hb, rfl⟩)
      · intro x y hx hy; rw [smul_add]; exact Submodule.add_mem _ hx hy
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact mem_smulSubmodule.mpr ⟨a * b, Submodule.mul_mem_mul ha hb, smul_mul' g a b⟩

/-- The `G`-action on `FractionalIdeal S P` induced by compatible actions on `R` and `P`. -/
@[reducible]
def mulDistribMulAction : MulDistribMulAction G (FractionalIdeal S P) where
  smul := smulFractional hS
  one_smul := smulFractional_one hS
  mul_smul := smulFractional_mul hS
  smul_one := smulFractional_smul_one hS
  smul_mul := smulFractional_smul_mul hS

end General

section FractionRing

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

/-- The `G`-action on `R` extends to a `G`-action on its fraction ring, via the unique
extension of each ring automorphism of `R` to the localization. -/
noncomputable instance fractionRingMulSemiringAction : MulSemiringAction G (FractionRing R) where
  smul g x := IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing R) (L := FractionRing R) (MulSemiringAction.toRingEquiv G R g) x
  one_smul x := by
    have : (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
        (MulSemiringAction.toRingEquiv G R (1 : G)) : FractionRing R →+* FractionRing R)
        = RingHom.id _ :=
      IsLocalization.ringHom_ext R⁰ (by ext r; simp)
    exact RingHom.congr_fun this x
  mul_smul g h x := by
    have : (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
        (MulSemiringAction.toRingEquiv G R (g * h)) : FractionRing R →+* FractionRing R) =
        (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
          (MulSemiringAction.toRingEquiv G R g) : FractionRing R →+* FractionRing R).comp
          (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
            (MulSemiringAction.toRingEquiv G R h)) :=
      IsLocalization.ringHom_ext R⁰ (by ext r; simp)
    exact RingHom.congr_fun this x
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

@[simp]
theorem fractionRing_smul_algebraMap (g : G) (r : R) :
    g • algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (g • r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (MulSemiringAction.toRingEquiv G R g) r

/-- Semilinearity over `R` of the action on the fraction ring. -/
theorem fractionRing_smul_smul (g : G) (a : R) (x : FractionRing R) :
    g • (a • x) = (g • a) • (g • x) := by
  rw [Algebra.smul_def, smul_mul', fractionRing_smul_algebraMap, ← Algebra.smul_def]

instance : SMulDistribClass G R (FractionRing R) where
  smul_distrib_smul := fractionRing_smul_smul

/-- The `G`-action on `R` induces a `G`-action on the fractional ideals of its fraction ring. -/
noncomputable instance instMulDistribMulActionFractionRing :
    MulDistribMulAction G (FractionalIdeal R⁰ (FractionRing R)) :=
  mulDistribMulAction (fun g _ hs => smul_mem_nonZeroDivisors g hs)

@[simp]
theorem mem_smul_fractionRing {g : G} {I : FractionalIdeal R⁰ (FractionRing R)}
    {y : FractionRing R} : y ∈ g • I ↔ ∃ x ∈ I, g • x = y := mem_smulFractional _

open scoped Pointwise in
/-- The coercion `Ideal R → FractionalIdeal R⁰ (FractionRing R)` is `G`-equivariant: the action
on ideals and the action on fractional ideals are compatible. -/
@[simp]
theorem coeIdeal_smul (g : G) (I : Ideal R) :
    (↑(g • I) : FractionalIdeal R⁰ (FractionRing R))
      = g • (I : FractionalIdeal R⁰ (FractionRing R)) := by
  refine coeToSubmodule_injective (Submodule.ext fun y => ?_)
  simp only [coe_coeIdeal, IsLocalization.mem_coeSubmodule]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨algebraMap R (FractionRing R) (g⁻¹ • b),
      ⟨g⁻¹ • b, (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mp hb, rfl⟩, ?_⟩
    show g • algebraMap R (FractionRing R) (g⁻¹ • b) = algebraMap R (FractionRing R) b
    rw [fractionRing_smul_algebraMap, smul_inv_smul]
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g • a, Ideal.smul_mem_pointwise_smul g a I ha,
      (fractionRing_smul_algebraMap g a).symm⟩

/-- The action on fractional ideals is compatible with `spanSingleton`. -/
@[simp]
theorem spanSingleton_smul (g : G) (x : FractionRing R) :
    g • spanSingleton R⁰ x = spanSingleton R⁰ (g • x) := by
  ext y
  simp only [mem_smul_fractionRing, mem_spanSingleton]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨g • a, (fractionRing_smul_smul g a x).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(g⁻¹ • a) • x, ⟨g⁻¹ • a, rfl⟩, by rw [fractionRing_smul_smul, smul_inv_smul]⟩

end FractionRing

end FractionalIdeal
