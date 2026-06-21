module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Tame ramification: the tame character (skeleton)

Filtration-free construction and properties of the tame character of a tamely ramified prime,
following the blueprint section "Tame ramification". Statements only; proofs are `sorry`.

The setting follows `Mathlib.RingTheory.Frobenius` / `Mathlib.RingTheory.Invariant.Basic`: a group
`G` acting on `S` over a base ring `R` (`[MulSemiringAction G S] [SMulCommClass G R S]`) and a
prime `Q : Ideal S`. The decomposition group is `MulAction.stabilizer G Q`; the inertia group is
`Q.inertia (MulAction.stabilizer G Q)`, a *normal* subgroup of it (`Ideal` pointwise API). The
residue field is `S ⧸ Q`, the base residue cardinality is `N𝔭 = Nat.card (R ⧸ Q.under R)`, and the
arithmetic Frobenius is `arithFrobAt R G Q` (`AlgHom.IsArithFrobAt`).

These are intended for eventual upstreaming to Mathlib.
-/

@[expose] public section

namespace Ideal

open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

variable (G) in
/-- The **tame character** `θ : I(Q) → (S ⧸ Q)ˣ`, `τ ↦ τ(π)/π`, attached to a uniformizer `π`
of the localization of `S` at `Q`. -/
noncomputable def tameCharacter (Q : Ideal S) [Q.IsMaximal]
    (π : Localization.AtPrime Q) (hπ : Irreducible π) :
    Q.inertia (MulAction.stabilizer G Q) →* (S ⧸ Q)ˣ :=
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
    (τ : Q.inertia (MulAction.stabilizer G Q))
    (hord : (orderOf τ).Coprime (ringChar (S ⧸ Q)))
    (h : tameCharacter G Q π hπ τ = 1) : τ = 1 :=
  sorry

/-- **Frobenius equivariance**: conjugating an inertia element by an arithmetic Frobenius
raises the tame character to the `N𝔭`-th power. (Conjugation lands back in inertia by
normality, via `MulAut.conjNormal`.) -/
theorem tameCharacter_conj (Q : Ideal S) [Q.IsMaximal]
    (π : Localization.AtPrime Q) (hπ : Irreducible π)
    (σ : MulAction.stabilizer G Q) (hσ : IsArithFrobAt R (σ : G) Q)
    (τ : Q.inertia (MulAction.stabilizer G Q)) :
    tameCharacter G Q π hπ (MulAut.conjNormal σ τ)
      = tameCharacter G Q π hπ τ ^ Nat.card (R ⧸ Q.under R) :=
  sorry

/-- **Tame inertia is cyclic**: if the order of the inertia group is prime to the residue
characteristic (tame ramification), the inertia group is cyclic. -/
theorem isCyclic_inertia (Q : Ideal S) [Q.IsMaximal]
    (htame : (Nat.card (Q.inertia (MulAction.stabilizer G Q))).Coprime (ringChar (S ⧸ Q))) :
    IsCyclic (Q.inertia (MulAction.stabilizer G Q)) :=
  sorry

/-- **Abelian tame ramification**: for an abelian action, the order of the inertia group
(the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one (Q : Ideal S) [Q.IsMaximal]
    [Finite G] [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)] [IsMulCommutative G]
    (htame : (Nat.card (Q.inertia (MulAction.stabilizer G Q))).Coprime (ringChar (S ⧸ Q))) :
    Nat.card (Q.inertia (MulAction.stabilizer G Q)) ∣ Nat.card (R ⧸ Q.under R) - 1 :=
  sorry

end Ideal
