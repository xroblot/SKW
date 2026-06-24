module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

public import SKW.Prereqs.Cotangent

/-!
# Tame ramification: the tame character (skeleton)

Filtration-free construction and properties of the tame character of a prime, following the
blueprint section "Tame ramification". Statements only; proofs are `sorry`.

The setting is the one of `Mathlib.RingTheory.Frobenius` / `Mathlib.RingTheory.Invariant.Basic`: a
group `G` acting on `S` over a base ring `R` (`[MulSemiringAction G S] [SMulCommClass G R S]`) and an
ideal `Q : Ideal S`. The decomposition group is `MulAction.stabilizer G Q`; the inertia group is
`Q.inertia (MulAction.stabilizer G Q)`, a *normal* subgroup of it, characterized as the kernel of
the action on the residue field `S ⧸ Q` (`IsFractionRing.ker_stabilizerHom`). The base residue
cardinality is `N𝔭 = Nat.card (R ⧸ Q.under R)` and the arithmetic Frobenius is `arithFrobAt R G Q`.

## The character

An inertia element `τ` acts trivially on `S ⧸ Q`, so the action it induces on the cotangent space
`Q ⧸ Q ^ 2` (an `S ⧸ Q`-module) is `S ⧸ Q`-linear; being induced by an automorphism it is an
`S ⧸ Q`-linear automorphism. The **tame character** is its determinant:
`θ(τ) := LinearMap.det (τ acting on Q ⧸ Q ^ 2) ∈ (S ⧸ Q)ˣ`. This needs no hypothesis on `Q`, is a
homomorphism for free (`det` is multiplicative), and lands in the units (`det` of an automorphism).
When `Q` is a maximal ideal with a uniformizer `π` of multiplicity one, `Q ⧸ Q ^ 2` is a line over
the field `S ⧸ Q` and `θ(τ)` is the scalar with `τ • π ≡ θ(τ) • π mod Q ^ 2`, i.e. `τ(π)/π`.

The properties below (rigidity, Frobenius equivariance, cyclicity of tame inertia, and the
divisibility `e ∣ N𝔭 - 1` in the abelian case) carry the extra hypotheses they need
(`[IsDedekindDomain S]`, maximality, finiteness, tameness).

-/

@[expose] public section

namespace Ideal

open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- An element of the stabilizer of `Q` preserves `Q`. -/
theorem smul_mem_of_mem_stabilizer (Q : Ideal S) (σ : MulAction.stabilizer G Q) {x : S}
    (hx : x ∈ Q) : σ • x ∈ Q := by
  nth_rewrite 1 [← (MulAction.mem_stabilizer_iff.mp σ.prop)]
  exact smul_mem_pointwise_smul σ x Q hx

variable (G) in
/-- The `S`-linear map `Q →ₗ[S] Q ⧸ Q ^ 2`, `x ↦ (τ • x)‾`. It is genuinely `S`-linear (not merely
`R`-linear): for `τ` in the inertia group `τ • s - s ∈ Q`, and the `τ`-semilinearity collapses
modulo `Q ^ 2`. -/
@[simps]
noncomputable def cotangentPreLift (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q)) :
    Q →ₗ[S] Q.Cotangent where
  toFun x := Q.toCotangent ⟨(τ : G) • (x : S), smul_mem_of_mem_stabilizer Q τ.1 x.2⟩
  map_add' x y := by simp [← map_add]
  map_smul' s x := by
    simp only [SetLike.val_smul, smul_eq_mul, smul_mul', RingHom.id_apply, ← map_smul,
      SetLike.mk_smul_mk, toCotangent_eq]
    rw [show (τ : G) • s * (τ : G) • x - s * (τ : G) • x = ((τ : G) • s - s) * ((τ : G) • x) by
      ring]
    exact pow_two Q ▸ mul_mem_mul (τ.prop s) (smul_mem_of_mem_stabilizer _ _ x.prop)

variable (G) in
/-- The map `x̄ ↦ mk (τ • x)` on the cotangent space `Q ⧸ Q ^ 2`, as a `S`-linear map. -/
noncomputable def cotangentLift (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q)) :
    Q.Cotangent →ₗ[S] Q.Cotangent :=
  Cotangent.lift (cotangentPreLift G Q τ) fun x y ↦ by
    simpa [toCotangent_eq_zero] using
      pow_two Q ▸ mul_mem_mul (smul_mem_of_mem_stabilizer Q τ.val x.prop)
        (smul_mem_of_mem_stabilizer Q τ.val y.prop)

@[simp]
theorem cotangentLift_toCotangent (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q)) (x : Q) :
    cotangentLift G Q τ (Q.toCotangent x) = cotangentPreLift G Q τ x :=
  Ideal.Cotangent.lift_toCotangent _ _ _

@[simp]
theorem cotangentLift_one (Q : Ideal S) :
    cotangentLift G Q 1 = 1 := by
  ext z
  obtain ⟨x, rfl⟩ := Q.toCotangent_surjective z
  simp

theorem cotangentLift_mul_apply (Q : Ideal S) (σ τ : Q.inertia (MulAction.stabilizer G Q))
    (z : Q.Cotangent) :
    cotangentLift G Q (σ * τ) z = cotangentLift G Q σ (cotangentLift G Q τ z) := by
  obtain ⟨x, rfl⟩ := Q.toCotangent_surjective z
  simp [mul_smul]

variable (G) in
/-- The cotangent action of an inertia element as a `S`-linear equivalence; the inverse
is the action of `τ⁻¹`. -/
noncomputable def cotangentEquiv (Q : Ideal S)
    (τ : Q.inertia (MulAction.stabilizer G Q)) : Q.Cotangent ≃ₗ[S] Q.Cotangent where
  __ := cotangentLift G Q τ
  invFun := cotangentLift G Q τ⁻¹
  left_inv x := by simp [← cotangentLift_mul_apply]
  right_inv z := by simp [← cotangentLift_mul_apply]

variable (G) in
/-- The natural `S ⧸ Q`-linear action of an inertia element on the cotangent space `Q ⧸ Q ^ 2`,
obtained from the `S`-linear action by extending scalars along `S → S ⧸ Q`. -/
noncomputable def cotangentEquivOfInertia (Q : Ideal S)
    (τ : Q.inertia (MulAction.stabilizer G Q)) : Q.Cotangent ≃ₗ[S ⧸ Q] Q.Cotangent :=
  LinearEquiv.extendScalarsOfSurjective Quotient.mk_surjective (cotangentEquiv G Q τ)

@[simp]
theorem cotangentEquivOfInertia_apply (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q))
    (z : Q.Cotangent) : cotangentEquivOfInertia G Q τ z = cotangentLift G Q τ z := rfl

variable (G) in
/-- The natural `S ⧸ Q`-linear action of inertia on the cotangent space `Q ⧸ Q ^ 2`. -/
@[simps]
noncomputable def cotangentInertiaAction (Q : Ideal S) :
    Q.inertia (MulAction.stabilizer G Q) →* (Q.Cotangent ≃ₗ[S ⧸ Q] Q.Cotangent) where
  toFun := cotangentEquivOfInertia G Q
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [cotangentLift_mul_apply]

variable (G) in
/-- The **tame character** `θ : I(Q) → (S ⧸ Q)ˣ`, the determinant of the `S ⧸ Q`-linear action of an
inertia element on the cotangent space `Q ⧸ Q ^ 2`. -/
noncomputable def tameCharacter (Q : Ideal S) :
    Q.inertia (MulAction.stabilizer G Q) →* (S ⧸ Q)ˣ :=
  LinearEquiv.det.comp (cotangentInertiaAction G Q)

theorem tameCharacter_def (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q)) :
    tameCharacter G Q τ = (cotangentInertiaAction G Q τ).det := rfl

open Module

variable [IsDedekindDomain S]

/-- (Rigidity, L1) If `θ(τ) = 1` then `τ` fixes the cotangent line `Q ⧸ Q ^ 2`: for `x ∈ Q`,
`τ • x ≡ x mod Q ^ 2`. Uses that `Q ⧸ Q ^ 2` is one-dimensional over the field `S ⧸ Q`, so
`det = 1` forces the action to be the identity. -/
theorem sub_mem_sq_of_tameCharacter_eq_one (Q : Ideal S) [Q.IsMaximal]
    (τ : Q.inertia (MulAction.stabilizer G Q)) (h : tameCharacter G Q τ = 1) {x : S} (hx : x ∈ Q) :
    (τ : G) • x - x ∈ Q ^ 2 := by
  let := Ideal.Quotient.field Q
  have : finrank (S ⧸ Q) Q.Cotangent = 1 := by

    sorry
  have : cotangentInertiaAction G Q τ = 1 := by
    rw [tameCharacter_def, Units.ext_iff, LinearEquiv.coe_det ] at h
    have := (LinearMap.det_eq_one_iff_eq_id this (cotangentInertiaAction G Q τ)).mp h
    rwa [← LinearEquiv.toLinearMap_inj]
  simpa [toCotangent_eq] using LinearEquiv.congr_fun this (Q.toCotangent ⟨x, hx⟩)

/-- (Rigidity, L2) Multiplicativity of `τ` propagates the order-two vanishing along the `Q`-adic
filtration: from `τ • x ≡ x mod Q ^ 2` on `Q`, one gets `τ • x ≡ x mod Q ^ (n + 2)` on `Q ^ (n+1)`. -/
theorem sub_mem_pow_succ_of_sub_mem_sq (Q : Ideal S)
    (τ : Q.inertia (MulAction.stabilizer G Q)) (h : ∀ x ∈ Q, (τ : G) • x - x ∈ Q ^ 2)
    (n : ℕ) {x : S} (hx : x ∈ Q ^ (n + 1)) : (τ : G) • x - x ∈ Q ^ (n + 2) :=
  sorry

/-- (Rigidity, L3) If `τ` is inertia, fixes every graded piece, and has order prime to the residue
characteristic, then `τ • x ≡ x` modulo every power of `Q`. Proof: `τ ^ m = id + m·δ + …` with
`δ = τ - id`; since `m` is a unit in `S ⧸ Q`, the bound on `δ` improves by one at each power. -/
theorem sub_mem_pow_of_coprime (Q : Ideal S) [Q.IsMaximal]
    (τ : Q.inertia (MulAction.stabilizer G Q)) (hbase : ∀ x : S, (τ : G) • x - x ∈ Q)
    (hstep : ∀ n : ℕ, ∀ x ∈ Q ^ (n + 1), (τ : G) • x - x ∈ Q ^ (n + 2))
    (hord : (orderOf τ).Coprime (ringChar (S ⧸ Q))) (n : ℕ) (x : S) :
    (τ : G) • x - x ∈ Q ^ n :=
  sorry

/-- (Rigidity, L4) An inertia element acting trivially on `S` is trivial. Uses Krull's intersection
theorem (`⋂ₙ Q ^ n = ⊥`) to pass from "trivial modulo every power" to "trivial", and faithfulness
of the action to conclude `τ = 1`. -/
theorem eq_one_of_forall_sub_mem_pow [FaithfulSMul G S] (Q : Ideal S) [Q.IsMaximal]
    (τ : Q.inertia (MulAction.stabilizer G Q))
    (h : ∀ (n : ℕ) (x : S), (τ : G) • x - x ∈ Q ^ n) : τ = 1 :=
  sorry

/-- **Rigidity** (filtration-free): an inertia element of order prime to the residue
characteristic on which the tame character vanishes is trivial. -/
theorem eq_one_of_tameCharacter_eq_one [FaithfulSMul G S] (Q : Ideal S) [Q.IsMaximal]
    (τ : Q.inertia (MulAction.stabilizer G Q)) (hord : (orderOf τ).Coprime (ringChar (S ⧸ Q)))
    (h : tameCharacter G Q τ = 1) : τ = 1 := by
  have hbase : ∀ x : S, (τ : G) • x - x ∈ Q := fun x => by
    simpa [MulAction.subgroup_smul_def] using AddSubgroup.mem_inertia.mp τ.2 x
  have hstep : ∀ n : ℕ, ∀ x ∈ Q ^ (n + 1), (τ : G) • x - x ∈ Q ^ (n + 2) :=
    fun n _ hx => sub_mem_pow_succ_of_sub_mem_sq Q τ
      (fun _ hy => sub_mem_sq_of_tameCharacter_eq_one Q τ h hy) n hx
  exact eq_one_of_forall_sub_mem_pow Q τ (sub_mem_pow_of_coprime Q τ hbase hstep hord)

/-- **Frobenius equivariance**: conjugating an inertia element by an arithmetic Frobenius
raises the tame character to the `N 𝔭`-th power. (Conjugation lands back in inertia by
normality, via `MulAut.conjNormal`.) -/
theorem tameCharacter_conj (Q : Ideal S) [Q.IsMaximal] (σ : MulAction.stabilizer G Q)
    (hσ : IsArithFrobAt R (σ : G) Q) (τ : Q.inertia (MulAction.stabilizer G Q)) :
    tameCharacter G Q (MulAut.conjNormal σ τ) = tameCharacter G Q τ ^ Nat.card (R ⧸ Q.under R) := by
  sorry

/-- **Tame inertia is cyclic**: if the order of the inertia group is prime to the residue
characteristic (tame ramification), the inertia group is cyclic. -/
theorem isCyclic_inertia (Q : Ideal S) [Q.IsMaximal]
    (htame : (Nat.card (Q.inertia (MulAction.stabilizer G Q))).Coprime (ringChar (S ⧸ Q))) :
    IsCyclic (Q.inertia (MulAction.stabilizer G Q)) := by
  sorry

/-- **Abelian tame ramification**: for an abelian action, the order of the inertia group
(the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one (Q : Ideal S) [Q.IsMaximal] [Finite G]
    [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)] [IsMulCommutative G]
    (htame : (Nat.card (Q.inertia (MulAction.stabilizer G Q))).Coprime (ringChar (S ⧸ Q))) :
    Nat.card (Q.inertia (MulAction.stabilizer G Q)) ∣ Nat.card (R ⧸ Q.under R) - 1 := by
  sorry

end Ideal

end
