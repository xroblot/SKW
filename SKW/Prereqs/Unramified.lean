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

/-!
# Transfer of `Algebra.IsUnramifiedIn` along an algebra isomorphism

If `S` and `S'` are isomorphic `R`-algebras, then a prime `𝔭` of `R` unramified in `S` is also
unramified in `S'`. Intended for eventual upstreaming.
-/

@[expose] public section

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
    [Algebra.EssFiniteType R T] [Algebra.IsIntegral S T] [IsDedekindDomain S] [FaithfulSMul S T]
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

end Algebra

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
    [Algebra K L] [IsScalarTower ℚ K L] (h : UnramifiedOutside L p) : UnramifiedOutside K p :=
  fun q hq hqp ↦ (h q hq hqp).tower_bot

open NumberField in
/-- A cyclotomic extension `ℚ(ζ_p)` is unramified outside `p`. -/
lemma unramifiedOutside_of_isCyclotomicExtension {K : Type*} [Field K] [NumberField K]
    [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] : UnramifiedOutside K p := by
  intro q hq hqp
  have : Fact q.Prime := ⟨hq⟩
  refine Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr fun 𝔓 _ h𝔓 ↦ ?_
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q K 𝔓
    (by rwa [Nat.prime_dvd_prime_iff_eq hq hp.out])

open NumberField IntermediateField in
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
    (ramificationIdx'_eq_one_iff.mpr (hKram q hq hqp _ (IsPrime.under (𝓞 K) 𝔮) hK))
    (ramificationIdx'_eq_one_iff.mpr (hFram q hq hqp _ (IsPrime.under (𝓞 F) 𝔮) hF)) hq₀

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
      ((RingOfIntegers.mapAlgEquiv (restrict_algEquiv le_sup_left)).restrictScalars ℤ)
  · exact fun q hq hqp ↦ (hFram q hq hqp).of_algEquiv
      ((RingOfIntegers.mapAlgEquiv (restrict_algEquiv le_sup_right)).restrictScalars ℤ)

end
