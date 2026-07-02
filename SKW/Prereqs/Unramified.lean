module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

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

end
