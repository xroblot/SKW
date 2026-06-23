module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

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

end Algebra

end
