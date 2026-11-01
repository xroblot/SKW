module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Localization.FractionRing

public import SKW.Prereqs.Ideals
public import SKW.Prereqs.Stickelberger

set_option linter.style.header false

@[expose] public section

/-!
# Fractional ideals

Bridges between `FractionalIdeal.count` and `multiplicity`, for a Dedekind domain `R` with
fraction field `K` and a maximal ideal `v`:

* `FractionalIdeal.count_coe_eq_multiplicity`: the `v`-adic valuation of an ideal `J` of `R` is
  `multiplicity v.asIdeal J`;
* `FractionalIdeal.count_coe_mul_inv_eq_multiplicity_sub`: the same for `I * J⁻¹`, with `I` and
  `J` nonzero ideals of `R`, as a difference of multiplicities;
* `FractionalIdeal.count_eq_multiplicity_num_sub`: the same for a nonzero fractional ideal `I`,
  written via `I.num` and `I.den`.

The commented-out block (action of a group on fractional ideals) is a copy of code now in
`SKW.Prereqs.Stickelberger`.
-/

-- Copied to `SKW.Prereqs.Stickelberger`.
/-
namespace FractionalIdeal

section General

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]
  {G : Type*} [Group G] [MulSemiringAction G R] [MulSemiringAction G P] [SMulDistribClass G R P]

/-- The image of a submodule `N ⊆ P` under the ring automorphism induced by `g`. -/
def smulSubmodule (g : G) (N : Submodule R P) : Submodule R P where
  carrier := (g • · : P → P) '' N
  add_mem' := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a + b, N.add_mem ha hb,
    smul_add g a b⟩
  zero_mem' := ⟨0, N.zero_mem, smul_zero g⟩
  smul_mem' c y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨(g⁻¹ • c) • x, N.smul_mem _ hx, ?_⟩
    change g • ((g⁻¹ • c) • x) = c • (g • x)
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
    change g • algebraMap R (FractionRing R) (g⁻¹ • b) = algebraMap R (FractionRing R) b
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
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped Pointwise

variable {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- A group acting on `R` by ring automorphisms acts on the height one primes of `R`. -/
instance : MulAction G (HeightOneSpectrum R) where
  smul g v := ⟨g • v.asIdeal, inferInstance, by simpa [Ideal.smul_eq_bot_iff] using v.ne_bot⟩
  one_smul v := HeightOneSpectrum.ext (one_smul G v.asIdeal)
  mul_smul g h v := HeightOneSpectrum.ext (mul_smul g h v.asIdeal)

@[simp]
theorem smul_asIdeal (g : G) (v : HeightOneSpectrum R) : (g • v).asIdeal = g • v.asIdeal := rfl

theorem smul_eq_equivOfRingEquiv (g : G) (v : HeightOneSpectrum R) :
    g • v = equivOfRingEquiv (MulSemiringAction.toRingEquiv G R g) v := by
  apply HeightOneSpectrum.ext
  rw [smul_asIdeal, equivOfRingEquiv_apply_asIdeal, Ideal.pointwise_smul_def', Ideal.mapEquiv_apply]

end IsDedekindDomain.HeightOneSpectrum

section count

open scoped nonZeroDivisors

open IsDedekindDomain HeightOneSpectrum FractionalIdeal Associates UniqueFactorizationMonoid

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The `v`-adic valuation of an ideal `J` is the multiplicity of `v` in `J`. -/
theorem FractionalIdeal.count_coe_eq_multiplicity (J : Ideal R) :
    count K v J = multiplicity v.asIdeal J := by
  obtain rfl | hJ := eq_or_ne J 0
  · simp [FractionalIdeal.count_zero]
  rw [count_coe K v hJ, Ideal.count_associates_factors_eq hJ v.isPrime v.ne_bot,
    count_normalizedFactors_eq_multiplicity hJ]

/-- The `v`-adic valuation of `I * J⁻¹`, for nonzero ideals `I` and `J`, is the difference of the
multiplicities of `v` in `I` and `J`. -/
theorem FractionalIdeal.count_coe_mul_inv_eq_multiplicity_sub {I J : Ideal R} (hI : I ≠ 0)
    (hJ : J ≠ 0) :
    count K v (I * (J : FractionalIdeal R⁰ K)⁻¹) =
      multiplicity v.asIdeal I - multiplicity v.asIdeal J := by
  rw [count_mul K v (coeIdeal_ne_zero.mpr hI) (inv_ne_zero (coeIdeal_ne_zero.mpr hJ)), count_inv,
    count_coe_eq_multiplicity, count_coe_eq_multiplicity, sub_eq_add_neg]

/-- The `v`-adic valuation of a nonzero fractional ideal `I` is the difference of the
multiplicities of `v` in `I.num` and in the ideal spanned by `I.den`. -/
theorem FractionalIdeal.count_eq_multiplicity_num_sub {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    count K v I =
      multiplicity v.asIdeal I.num - multiplicity v.asIdeal (Ideal.span {(I.den : R)}) := by
  rw [← count_coe_mul_inv_eq_multiplicity_sub K v (num_eq_zero_iff.not.mpr hI) (by simp),
    coeIdeal_span_singleton, ← den_mul_self_eq_num', mul_comm, inv_mul_cancel_left₀ (by simp)]

end count

section FractionalIdealCount

open scoped nonZeroDivisors
open IsDedekindDomain HeightOneSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S]
  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L]

theorem FractionalIdeal.extended_eq_map_num_mul_inv {f : R →+* S} (hf : R⁰ ≤ S⁰.comap f)
    (I : FractionalIdeal R⁰ K) :
    I.extended L hf = (I.num.map f) * (Ideal.span {f I.den} : FractionalIdeal S⁰ L)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq₀, mul_comm]
  · rw [← Set.image_singleton, ← Ideal.map_span, ← extended_coeIdeal_eq_map (K := K) L hf,
      ← extended_mul, coeIdeal_span_singleton, den_mul_self_eq_num', extended_coeIdeal_eq_map]
  · rw [coeIdeal_ne_zero, ne_eq, Ideal.span_singleton_eq_bot, ← ne_eq]
    exact nonZeroDivisors.ne_zero (hf I.den.2)

theorem FractionalIdeal.ringEquivOfRingEquiv_eq_extended [IsDomain R] (f : R ≃+* S)
    (I : FractionalIdeal R⁰ K) :
    ringEquivOfRingEquiv K L f I =
      I.extended L (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (f : R →+* S)
        fun _ _ h ↦ f.injective h) := by
  rw [← coeToSubmodule_inj, coe_extended_eq_span, ringEquivOfRingEquiv_apply, coe_mk,
    ← Submodule.span_eq (Submodule.map _ _), Submodule.map_coe]
  rfl

theorem FractionalIdeal.ringEquivOfRingEquiv_eq_map_num_mul_inv [IsDomain R] (f : R ≃+* S)
    (I : FractionalIdeal R⁰ K) :
    ringEquivOfRingEquiv K L f I =
      (I.num.map f) * (Ideal.span {f I.den} : FractionalIdeal S⁰ L)⁻¹ := by
  rw [ringEquivOfRingEquiv_eq_extended, extended_eq_map_num_mul_inv, Ideal.map_coe,
    RingEquiv.coe_toRingHom]

theorem FractionalIdeal.count_ringEquivOfRingEquiv [IsDedekindDomain R] (f : R ≃+* S)
    (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) :
    count L (equivOfRingEquiv f v) (ringEquivOfRingEquiv K L f I) = count K v I := by
  by_cases hI : I = 0
  · simp [hI, count_zero]
  rw [ringEquivOfRingEquiv_eq_map_num_mul_inv, ← Ideal.mapEquiv_apply, count_mul, count_inv,
    count_coe_eq_multiplicity, count_coe_eq_multiplicity, equivOfRingEquiv_apply_asIdeal,
    ← Set.image_singleton, ← Ideal.map_span, ← Ideal.mapEquiv_apply, ← Ideal.mapEquiv_apply,
    multiplicity_map_eq, multiplicity_map_eq, Int.add_neg_eq_sub,
    ← count_eq_multiplicity_num_sub _ _ hI]
  · rw [coeIdeal_ne_zero, ne_eq, Ideal.mapEquiv_eq_bot_iff]
    exact num_eq_zero_iff.not.mpr hI
  · simp [- spanSingleton_inv]

theorem FractionalIdeal.count_smul [IsDedekindDomain R] {G : Type*} [Group G]
    [MulSemiringAction G R] [MulSemiringAction G K] [SMulDistribClass G R K]
    (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) (σ : G) :
    count K (σ • v) (σ • I) = count K v I := by
  rw [← count_ringEquivOfRingEquiv K K (MulSemiringAction.toRingEquiv G R σ) v I]
  congr
  · rw [← smul_eq_equivOfRingEquiv]
  -- TODO: the `have` below is missing API, a lemma stating
  -- `IsFractionRing.ringEquivOfRingEquiv (toRingEquiv G R σ) = toRingEquiv G K σ`.
  -- This goal should be revisited once the action on fractional ideals is defined via `extended`
  -- (see `SKW/Sandbox.lean`), since the proof depends on that definition.
  · ext x
    rw [mem_smul, ← mem_coe, ringEquivOfRingEquiv_apply, coe_mk, Submodule.mem_map]
    have : (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
        (MulSemiringAction.toRingEquiv G R σ)).toRingHom = MulSemiringAction.toRingHom G K σ :=
      IsLocalization.ringHom_ext R⁰ <| RingHom.ext fun r ↦ by
        simp [algebraMap.smul']
    exact exists_congr fun y ↦ and_congr_right fun _ ↦
      Eq.congr_left (RingHom.congr_fun this y).symm

end FractionalIdealCount
