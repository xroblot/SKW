module

public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Ideal.Pointwise

set_option linter.style.header false

/-!
# PRed to Mathlib: group action on fractional ideals

The declarations in this file were extracted from `SKW.Prereqs.Stickelberger` and submitted
upstream as Mathlib PR [#46386](https://github.com/leanprover-community/mathlib4/pull/46386).
There the action is an instance in the `Pointwise` locale, only for `R⁰` (`extendedSMul` and
`extendedMulDistribMulAction` are dropped, `canonicalEquiv_apply` is inlined), `smul_def` is
renamed `pointwise_smul_def`, and `IsLocalization.map_toRingHom_apply` is inlined in
`spanSingleton_smul`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted, and the usages redirected to the
Mathlib versions (with `open scoped Pointwise`).
-/

@[expose] public section

theorem MulSemiringAction.toRingHom_mul {G R : Type*} [Monoid G] [Semiring R]
    [MulSemiringAction G R] (g h : G) :
    MulSemiringAction.toRingHom G R (g * h) =
      (MulSemiringAction.toRingHom G R g).comp (MulSemiringAction.toRingHom G R h) :=
  RingHom.ext fun x ↦ mul_smul g h x

theorem MulSemiringAction.toRingHom_one {G R : Type*} [Monoid G] [Semiring R]
    [MulSemiringAction G R] :
    MulSemiringAction.toRingHom G R 1 = RingHom.id R :=
  RingHom.ext fun x ↦ one_smul G x

namespace FractionalIdeal

noncomputable section ExtendedAction

variable {R : Type*} [CommRing R] {S : Submonoid R} (P : Type*) [CommRing P] [Algebra R P]
  [IsLocalization S P]

theorem extended_id (I : FractionalIdeal S P) :
    I.extended P (f := RingHom.id R)
      (fun _ h ↦ Submonoid.mem_comap.mpr h : S ≤ S.comap (RingHom.id R)) = I := by
  simp only [← coeToSubmodule_inj, coeToSubmodule_extended_eq_span, IsLocalization.map_id,
    Set.image_id']
  exact Submodule.span_eq _

theorem canonicalEquiv_apply (P' : Type*) [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (I : FractionalIdeal S P) :
    canonicalEquiv S P P' I = map (IsLocalization.algEquiv S P P').toAlgHom I := by
  ext; simp

theorem canonicalEquiv_eq_extended (P' : Type*) [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (I : FractionalIdeal S P) :
    canonicalEquiv S P P' I = I.extended P'
      (fun _ h ↦ Submonoid.mem_comap.mpr h : S ≤ S.comap (RingHom.id R)) := by
  rw [canonicalEquiv_apply, ← coeToSubmodule_inj, coe_map, coeToSubmodule_extended_eq_span,
    ← Submodule.span_eq (Submodule.map _ _)]
  rfl

variable {G : Type*} [Group G] [MulSemiringAction G R]
  (hS : ∀ g : G, S ≤ S.comap (MulSemiringAction.toRingHom G R g))

/-- The `G`-action on `FractionalIdeal S P` by extension along `MulSemiringAction.toRingHom`. -/
abbrev extendedSMul : SMul G (FractionalIdeal S P) where
  smul g I := I.extended P (hS g)

theorem extendedSMul_def (g : G) (I : FractionalIdeal S P) :
    letI := extendedSMul P hS
    g • I = I.extended P (hS g) := rfl

/-- The `G`-action on `FractionalIdeal S P` induced by an action on `R` preserving `S`. -/
abbrev extendedMulDistribMulAction : MulDistribMulAction G (FractionalIdeal S P) :=
{ __ := extendedSMul P hS
  smul_one _ := extended_one _ _
  one_smul I := by
    simp_rw [extendedSMul_def, MulSemiringAction.toRingHom_one]
    exact extended_id _ I
  smul_mul _ _ _ := extended_mul _ _ _ _
  mul_smul g h I := by
    simp_rw [extendedSMul_def, MulSemiringAction.toRingHom_mul]
    exact (extended_extended _ (hS h) I (hS g)).symm }

end ExtendedAction

section FractionField

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
  {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- The `G`-action on `R` induces a `G`-action on the fractional ideals of `K`. -/
noncomputable instance : MulDistribMulAction G (FractionalIdeal R⁰ K) :=
  extendedMulDistribMulAction _
    fun g _ hs ↦ Submonoid.mem_comap.mpr (smul_mem_nonZeroDivisors g hs)

theorem smul_def (g : G) (I : FractionalIdeal R⁰ K) :
    g • I = I.extended K (f := MulSemiringAction.toRingHom G R g) (N := R⁰)
      (fun _ hs ↦ Submonoid.mem_comap.mpr (smul_mem_nonZeroDivisors g hs)) := rfl

theorem canonicalEquiv_smul (K' : Type*) [CommRing K'] [Algebra R K'] [IsFractionRing R K'] (g : G)
    (I : FractionalIdeal R⁰ K) :
    canonicalEquiv R⁰ K K' (g • I) = g • canonicalEquiv R⁰ K K' I := by
  rw [canonicalEquiv_eq_extended, canonicalEquiv_eq_extended, smul_def, smul_def,
    extended_extended, extended_extended]

open scoped Pointwise in
/-- The coercion `Ideal R → FractionalIdeal R⁰ K` is `G`-equivariant: the action on ideals and the
action on fractional ideals are compatible. -/
@[simp]
theorem coeIdeal_smul (g : G) (I : Ideal R) :
    (↑(g • I) : FractionalIdeal R⁰ K) = g • (I : FractionalIdeal R⁰ K) := by
  rw [smul_def, extended_coeIdeal_eq_map, Ideal.pointwise_smul_def]

variable [MulSemiringAction G K] [SMulDistribClass G R K]

/-- The localization of `toRingHom G R g` is the action of `g` on `K`. -/
theorem _root_.IsLocalization.map_toRingHom_apply (g : G) (x : K) :
    IsLocalization.map K (MulSemiringAction.toRingHom G R g)
      (fun _ hs ↦ Submonoid.mem_comap.mpr (smul_mem_nonZeroDivisors g hs) :
        R⁰ ≤ R⁰.comap (MulSemiringAction.toRingHom G R g)) x = g • x :=
  RingHom.congr_fun (g := MulSemiringAction.toRingHom G K g)
    (IsLocalization.ringHom_ext R⁰ <| RingHom.ext fun a ↦ by
      simp [algebraMap.smul']) x

/-- The action on fractional ideals is compatible with `spanSingleton`. -/
theorem spanSingleton_smul (g : G) (x : K) :
    g • spanSingleton R⁰ x = spanSingleton R⁰ (g • x) := by
  rw [smul_def, extended_spanSingleton, IsLocalization.map_toRingHom_apply]

end FractionField

end FractionalIdeal
