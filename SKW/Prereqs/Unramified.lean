module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

public import SKW.Prereqs.OtherPR
public import SKW.Prereqs.NumberField

set_option linter.style.header false

/-!
# Transfer of `Algebra.IsUnramifiedIn` along an algebra isomorphism

If `S` and `S'` are isomorphic `R`-algebras, then a prime `𝔭` of `R` unramified in `S` is also
unramified in `S'`. Intended for eventual upstreaming.
-/

@[expose] public section

/-- If `G` is a finite Galois group of `L/K`, then `L/K` is separable. -/
theorem IsGaloisGroup.isSeparable (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L]
    [MulSemiringAction G L] [Finite G] [IsGaloisGroup G K L] : Algebra.IsSeparable K L :=
  have := IsGaloisGroup.isGalois G K L
  inferInstance

namespace Algebra

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S']

/-- `Algebra.IsUnramifiedIn` transfers along an isomorphism of `R`-algebras. -/
theorem IsUnramifiedIn.of_algEquiv (e : S ≃ₐ[R] S') {𝔭 : Ideal R}
    (h : Algebra.IsUnramifiedIn S 𝔭) : Algebra.IsUnramifiedIn S' 𝔭 := by
  intro 𝔔 _ hlo
  have : IsUnramifiedAt R (𝔔.comap e) := h _ inferInstance inferInstance
  exact FormallyUnramified.of_equiv (Localization.localAlgEquiv (𝔔.comap e) 𝔔 e rfl)

/-- Unramifiedness descends to the bottom of a tower `R → S → T`: if a prime `𝔭` of `R` is
unramified in the top ring `T`, then it is unramified in the intermediate ring `S`. This is the
ring-tower generalisation of "a subfield of an extension unramified at `𝔭` is itself unramified
at `𝔭`". -/
theorem IsUnramifiedIn.tower_bot {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra.EssFiniteType R S]
    [Algebra.EssFiniteType R T] [Algebra.IsIntegral S T] [FaithfulSMul S T]
    [Module.Flat S T] [IsDomain T]
    {𝔭 : Ideal R} (h : Algebra.IsUnramifiedIn T 𝔭) :
    Algebra.IsUnramifiedIn S 𝔭 := by
  intro P _ _
  obtain ⟨Q, hQ₁, _⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat P (B := T)
  have := h Q hQ₁ (Ideal.LiesOver.trans Q P 𝔭)
  exact Algebra.IsUnramifiedAt.of_liesOver _ P Q

/-- Unramifiedness passes to the top of a tower `R → S → T`: if a prime `𝔭` of `R` is unramified
in `T` over `R`, then `T` is unramified over `S` at every prime `q` of `S` lying over `𝔭`. This is
the ring-tower generalisation of "the top of an extension unramified at `𝔭` is unramified over any
intermediate field". -/
theorem IsUnramifiedIn.tower_top {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {𝔭 : Ideal R} (h : Algebra.IsUnramifiedIn T 𝔭)
    (𝔓 : Ideal S) [𝔓.LiesOver 𝔭] : Algebra.IsUnramifiedIn T 𝔓 := by
  intro Q _ _
  have := h Q inferInstance (Ideal.LiesOver.trans Q 𝔓 𝔭)
  exact Algebra.IsUnramifiedAt.of_restrictScalars R Q

/-- Let `f : R ≃+* R'` and `g : S ≃+* S'` be ring isomorphisms compatible with the algebra maps.
If `𝔭` is unramified in `S`, then `𝔭.map f` is unramified in `S'`. -/
theorem IsUnramifiedIn.of_equiv_equiv {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S'] {f : R ≃+* R'} {g : S ≃+* S'}
    (hcomp : (algebraMap R' S').comp f = (g : S →+* S').comp (algebraMap R S)) {𝔭 : Ideal R}
    (h : Algebra.IsUnramifiedIn S 𝔭) : Algebra.IsUnramifiedIn S' (𝔭.map f) := by
  let : Algebra R R' := f.toRingHom.toAlgebra
  let : Algebra R S' := ((algebraMap R' S').comp f.toRingHom).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  have : (𝔭.map f).LiesOver 𝔭 := ⟨(Ideal.comap_map_of_bijective _ f.bijective).symm⟩
  let e : S ≃ₐ[R] S' := .ofRingEquiv (f := g) fun x ↦ (RingHom.congr_fun hcomp x).symm
  exact (h.of_algEquiv e).tower_top _

/-- Let `K` and `L` be fraction fields of `R` and `S`. If `L/K` is separable, then `S` is
unramified over `R` at the zero ideal. -/
theorem isUnramifiedAt_bot_of_isSeparable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsScalarTower R S L] [Algebra.IsSeparable K L] :
    IsUnramifiedAt R (⊥ : Ideal S) := by
  have : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal S).primeCompl)
  have : FormallyUnramified R K := .of_isLocalization (nonZeroDivisors R)
  have : FormallyUnramified K L := .of_isSeparable K L
  have : FormallyUnramified R L := .comp R K L
  exact .of_equiv ((IsLocalization.algEquiv (nonZeroDivisors S) _ L).restrictScalars R).symm

end Algebra

namespace Ideal.IsInertiaRing

open Ideal

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [Algebra C B] [IsScalarTower A C B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B] (P : Ideal B) [hP : P.IsPrime] {p : Ideal A} [P.LiesOver p]
  [hC : P.IsInertiaRing G C] [IsDomain A] [IsDomain B] [IsDomain C] [Module.Finite A B]
  [Module.Flat A B] [Module.Flat C B] [Ring.HasFiniteQuotients A] [Ring.HasFiniteQuotients B]
  [Algebra.EssFiniteType A C]

/-
Proof of `isUnramifiedAt`.

The ramification index of `P.under C` over `A` is `1` (`IsInertiaRing.ramificationIdx_eq` in
#35808). The residue fields are finite (`Ring.HasFiniteQuotients`), hence perfect, so the residue
field extension is separable, and `Ideal.ramificationIdx_eq_one_iff` concludes.
If `P = ⊥`, then `B` is a field, hence so are `A` and `C` (`isField_of_isIntegral_of_isField`).
The extension `C/A` is separable since `B/A` is Galois, and `isUnramifiedAt_bot_of_isSeparable`
concludes.
-/

attribute [local instance] FractionRing.liftAlgebra in
include G in
/-- The prime of an inertia ring `C` of `P` lying under `P` is unramified over `A`. -/
theorem isUnramifiedAt : Algebra.IsUnramifiedAt A (P.under C) := by
  obtain rfl | hP := eq_or_ne P ⊥
  · have : FaithfulSMul A C := .tower_bot A C B
    have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
      let := IsFractionRing.mulSemiringAction G B (FractionRing B)
      exact (IsGaloisGroup.to_isFractionRing G A B _ _).isSeparable G _ _
    have : Algebra.IsSeparable (FractionRing A) (FractionRing C) :=
      Algebra.isSeparable_tower_bot_of_isSeparable _ _ (FractionRing B)
    simpa using Algebra.isUnramifiedAt_bot_of_isSeparable (R := A) (S := C)
      (FractionRing A) (FractionRing C)
  · have : Algebra.IsIntegral A C := .tower_bot B
    have : NeZero (under A (under C P)) := ⟨by simpa [under_under] using under_ne_bot _ hP⟩
    rw [← ramificationIdx_eq_one_iff]
    exact IsInertiaRing.ramificationIdx_eq G P C (under C P) <| under_ne_bot _ hP

/-
Proof of `isUnramifiedIn`.

Let `𝓠` be a prime of `C` over `p` and `Q` a prime of `B` over `𝓠` (`Ideal.exists_ideal_liesOver`).
Then `Q = σ • P` for some `σ ∈ G` (`exists_smul_eq_of_isGaloisGroup`), so the inertia group of `Q`
is `σ (inertia G P) σ⁻¹ = inertia G P` since it is normal. Hence `C` is also an inertia ring of `Q`,
and `𝓠 = Q.under C` is unramified over `A` by `isUnramifiedAt` applied to `Q`.
-/

include G in
/-- If the inertia group of `P` is normal (e.g. if `G` is commutative), then `p` is unramified in
an inertia ring `C` of `P`. -/
theorem isUnramifiedIn [(inertia G P).Normal] : Algebra.IsUnramifiedIn C p := by
  have : Algebra.IsIntegral C B := .tower_top A
  intro 𝓠 h𝓠₁ h𝓠₂
  obtain ⟨Q, ⟨_, hQ⟩⟩ := Ideal.nonempty_primesOver (S := B) 𝓠
  have : Q.IsInertiaRing G C := by
    have : Q.LiesOver p := LiesOver.trans Q 𝓠 p
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup p P Q G
    have : inertia G Q = inertia G P := by
      rw [← hσ, inertia_smul]
      exact Subgroup.Normal.conj_smul_eq_self σ _
    exact { toIsGaloisGroup := this ▸ hC.toIsGaloisGroup }
  rw [liesOver_iff] at hQ
  simp_rw [hQ]
  exact isUnramifiedAt G Q

end Ideal.IsInertiaRing

open NumberField Ideal IntermediateField

/-- `K/ℚ` is unramified outside `p`: every prime `q ≠ p` is unramified in `𝓞 K`. -/
def UnramifiedOutside (K : Type*) [Field K] (p : ℕ) : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})

variable (p : ℕ)

open NumberField in
/-- `UnramifiedOutside` transfers along a `ℚ`-algebra isomorphism of number fields. -/
lemma UnramifiedOutside.of_algEquiv {K K' : Type*} [Field K] [Field K'] [NumberField K]
    [NumberField K'] (e : K ≃ₐ[ℚ] K') (h : UnramifiedOutside K p) : UnramifiedOutside K' p :=
  fun q hq hqp ↦ (h q hq hqp).of_algEquiv ((RingOfIntegers.mapAlgEquiv e).restrictScalars ℤ)

open NumberField in
/-- The bottom of a tower `ℚ → K → L` inherits unramifiedness: if `L` is unramified outside `p`, so
is the subfield `K` (a sub-extension of an unramified-outside-`p` extension is unramified outside
`p`). -/
lemma UnramifiedOutside.tower_bot {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (h : UnramifiedOutside L p) : UnramifiedOutside K p :=
  fun q hq hqp ↦ (h q hq hqp).tower_bot

open NumberField in
/-- A cyclotomic extension `ℚ(ζ_n)` is unramified at every prime not dividing `n`. -/
lemma isUnramifiedIn_of_isCyclotomicExtension {K : Type*} [Field K] [NumberField K] {n : ℕ}
    [NeZero n] [IsCyclotomicExtension {n} ℚ K] [Fact p.Prime] (hpn : ¬ p ∣ n) :
    Algebra.IsUnramifiedIn (𝓞 K) (span {(p : ℤ)}) := by
  refine Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun P _ hP ↦ ?_
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hpn

/-- The cyclotomic field `ℚ(ζ_{p ^ k})` is unramified outside `p`. -/
lemma UnramifiedOutside.of_isCyclotomicExtension (k : ℕ) (K : Type*) [Field K] [NumberField K]
    [hp : Fact p.Prime] [IsCyclotomicExtension {p ^ k} ℚ K] : UnramifiedOutside K p :=
  fun q hq hqp ↦
    have : Fact q.Prime := ⟨hq⟩
    isUnramifiedIn_of_isCyclotomicExtension q (n := p ^ k) fun h ↦
      hqp <| (Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow h)

/-- The cyclotomic field `ℚ(ζ_{p})` is unramified outside `p`. -/
lemma UnramifiedOutside.of_isCyclotomicExtension' (K : Type*) [Field K] [NumberField K]
    [Fact p.Prime] [hK : IsCyclotomicExtension {p } ℚ K] : UnramifiedOutside K p := by
  rw [← pow_one p] at hK
  exact .of_isCyclotomicExtension p 1 K

open NumberField IntermediateField in
/-- Let `K` and `F` be subfields of `L` with `K ⊔ F = ⊤`. If a nonzero ideal `p` of `ℤ` is
unramified in `𝓞 K` and in `𝓞 F`, then it is unramified in `𝓞 L`. -/
lemma isUnramifiedIn_sup' {L : Type*} [Field L] [NumberField L] (K F : IntermediateField ℚ L)
    (htop : K ⊔ F = ⊤) {p : Ideal ℤ} (hp : p ≠ ⊥) (hK : Algebra.IsUnramifiedIn (𝓞 K) p)
    (hF : Algebra.IsUnramifiedIn (𝓞 F) p) :
    Algebra.IsUnramifiedIn (𝓞 L) p := by
  refine Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun 𝔮 _ h𝔮 ↦ ?_
  have := LiesOver.tower_bot 𝔮 (under (𝓞 K) 𝔮) p
  have := LiesOver.tower_bot 𝔮 (under (𝓞 F) 𝔮) p
  exact ramificationIdx_sup_eq_one htop
    (ramificationIdx_eq_one_iff.mpr (hK _ (IsPrime.under (𝓞 K) 𝔮) inferInstance))
    (ramificationIdx_eq_one_iff.mpr (hF _ (IsPrime.under (𝓞 F) 𝔮) inferInstance)) hp

/-- Top-field version of `unramifiedOutside_sup`: if `K` and `F` are both unramified outside `p` and
together generate the whole field (`K ⊔ F = ⊤`), then `L` itself is unramified outside `p`. The
general form `unramifiedOutside_sup` (compositum inside an arbitrary ambient) reduces to this. -/
lemma unramifiedOutside_sup' {L : Type*} [Field L] [NumberField L] (K F : IntermediateField ℚ L)
    (hKram : UnramifiedOutside K p) (hFram : UnramifiedOutside F p) (htop : K ⊔ F = ⊤) :
    UnramifiedOutside L p := by
  intro q hq hqp
  have hq₀ : span {(q : ℤ)} ≠ ⊥ := by simpa using hq.ne_zero
  refine Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun 𝔮 _ h𝔮 ↦ ?_
  have hK := LiesOver.tower_bot 𝔮 (under (𝓞 K) 𝔮) (span {(q : ℤ)})
  have hF := LiesOver.tower_bot 𝔮 (under (𝓞 F) 𝔮) (span {(q : ℤ)})
  exact ramificationIdx_sup_eq_one htop (p := span {(q : ℤ)})
    (ramificationIdx_eq_one_iff.mpr (hKram q hq hqp _ (IsPrime.under (𝓞 K) 𝔮) hK))
    (ramificationIdx_eq_one_iff.mpr (hFram q hq hqp _ (IsPrime.under (𝓞 F) 𝔮) hF)) hq₀

set_option backward.isDefEq.respectTransparency false in
/-- The compositum `K ⊔ F` of two number fields, each unramified outside `p`, is itself unramified
outside `p`. -/
lemma unramifiedOutside_sup {A : Type*} [Field A] [CharZero A] (K F : IntermediateField ℚ A)
    [NumberField K] [NumberField F] (hKram : UnramifiedOutside K p)
    (hFram : UnramifiedOutside F p) :
    UnramifiedOutside ↑(K ⊔ F) p := by
  let F' : IntermediateField ℚ ↑(K ⊔ F) := F.restrict le_sup_right
  let K' : IntermediateField ℚ ↑(K ⊔ F) := K.restrict le_sup_left
  refine unramifiedOutside_sup' p K' F' ?_ ?_
    (lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_top]))
  · exact fun q hq hqp ↦ (hKram q hq hqp).of_algEquiv
      ((RingOfIntegers.mapAlgEquiv (restrictAlgEquiv (le_sup_left : K ≤ K ⊔ F))).restrictScalars ℤ)
  · exact fun q hq hqp ↦ (hFram q hq hqp).of_algEquiv
      ((RingOfIntegers.mapAlgEquiv (restrictAlgEquiv (le_sup_right : F ≤ K ⊔ F))).restrictScalars ℤ)

end
