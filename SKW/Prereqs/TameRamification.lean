module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Tame ramification: the tame character (skeleton)

Filtration-free construction and properties of the tame character of a tamely ramified prime,
following the blueprint section "Tame ramification". Statements only; proofs are `sorry`.

The setting follows `Mathlib.RingTheory.Frobenius`: a group `G` acting on `S` over a base ring
`R` (`[MulSemiringAction G S] [SMulCommClass G R S]`), and a prime `Q : Ideal S`. The inertia
group is `Ideal.inertia G Q`, the residue field is `S ⧸ Q`, and the residue cardinality of the
base prime is `N𝔭 = Nat.card (R ⧸ Q.under R)` (cf. `AlgHom.IsArithFrobAt`). The arithmetic
Frobenius is `arithFrobAt R G Q`.

These are intended for eventual upstreaming to Mathlib.
-/

@[expose] public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

variable (G) in
/-- The **tame character** `θ : I(Q) → (S ⧸ Q)ˣ`, `τ ↦ τ(π)/π`, attached to a uniformizer `π`
of the localization of `S` at `Q`. -/
noncomputable def tameCharacter (Q : Ideal S) [Q.IsMaximal]
    (π : Localization.AtPrime Q) (hπ : Irreducible π) :
    inertia G Q →* (S ⧸ Q)ˣ :=
  sorry

/-- The tame character does not depend on the chosen uniformizer. -/
theorem tameCharacter_eq (Q : Ideal S) [Q.IsMaximal]
    (π π' : Localization.AtPrime Q) (hπ : Irreducible π) (hπ' : Irreducible π') :
    tameCharacter G Q π hπ = tameCharacter G Q π' hπ' :=
  sorry

/-- **Rigidity** (filtration-free): an inertia element of order prime to the residue
characteristic on which the tame character vanishes is trivial. -/
theorem eq_one_of_tameCharacter_eq_one (Q : Ideal S) [Q.IsMaximal]
    (π : Localization.AtPrime Q) (hπ : Irreducible π)
    (τ : inertia G Q) (hord : (orderOf τ).Coprime (ringChar (S ⧸ Q)))
    (h : tameCharacter G Q π hπ τ = 1) : τ = 1 :=
  sorry

/-- **Frobenius equivariance**: conjugating an inertia element by an arithmetic Frobenius
raises the tame character to the `N𝔭`-th power. -/
theorem tameCharacter_conj (Q : Ideal S) [Q.IsMaximal]
    (π : Localization.AtPrime Q) (hπ : Irreducible π)
    {σ : G} (hσ : IsArithFrobAt R σ Q) (τ : inertia G Q)
    (hστ : σ * (τ : G) * σ⁻¹ ∈ inertia G Q) :
    tameCharacter G Q π hπ ⟨σ * τ * σ⁻¹, hστ⟩
      = tameCharacter G Q π hπ τ ^ Nat.card (R ⧸ Q.under R) :=
  sorry

/-- **Tame inertia is cyclic**: if the order of the inertia group is prime to the residue
characteristic (tame ramification), the inertia group is cyclic. -/
theorem isCyclic_inertia (Q : Ideal S) [Q.IsMaximal]
    (htame : (Nat.card (inertia G Q)).Coprime (ringChar (S ⧸ Q))) :
    IsCyclic (inertia G Q) :=
  sorry

/-- **Abelian tame ramification**: for an abelian action, the order of the inertia group
(the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one (Q : Ideal S) [Q.IsMaximal]
    [Finite G] [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)]
    (hab : ∀ a b : G, a * b = b * a)
    (htame : (Nat.card (inertia G Q)).Coprime (ringChar (S ⧸ Q))) :
    Nat.card (inertia G Q) ∣ Nat.card (R ⧸ Q.under R) - 1 :=
  sorry

end Ideal
