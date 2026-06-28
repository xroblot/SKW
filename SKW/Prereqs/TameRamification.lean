module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

public import SKW.Prereqs.Cotangent
public import SKW.Prereqs.AlgebraMisc

/-!
# Tame ramification: the tame character

Filtration-free construction and properties of the tame character of a prime, following the
blueprint section "Tame ramification".

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

/-- An arithmetic Frobenius `σ` acts on the residue ring `S ⧸ Q` as the `N𝔭`-th power map, for any
action of `σ` on `S ⧸ Q` compatible with its action on `S` (`SMulDistribClass`, giving
`σ • mk x = mk (σ • x)` via `algebraMap.smul'`). -/
theorem _root_.IsArithFrobAt.smul_residue {M : Type*} [Monoid M] [MulSemiringAction M S]
    [SMulCommClass M R S] {Q : Ideal S} [MulDistribMulAction M (S ⧸ Q)]
    [SMulDistribClass M S (S ⧸ Q)] {σ : M} (H : IsArithFrobAt R σ Q) (c : S ⧸ Q) :
    σ • c = c ^ Nat.card (R ⧸ Q.under R) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← Ideal.Quotient.algebraMap_eq, ← algebraMap.smul']
  exact H.mk_apply x

/-- A subgroup element is an arithmetic Frobenius if its image in `G` is (the subgroup acts via the
inclusion, so the actions agree definitionally). -/
theorem _root_.IsArithFrobAt.of_coe {H : Subgroup G} {σ : H} {Q : Ideal S}
    (h : IsArithFrobAt R (σ : G) Q) : IsArithFrobAt R σ Q := h

variable (G) in
/-- The **tame character** `θ : I(Q) → (S ⧸ Q)ˣ`, the determinant of the `S ⧸ Q`-linear action of an
inertia element on the cotangent space `Q ⧸ Q ^ 2`. -/
noncomputable def tameCharacter (Q : Ideal S) :
    Q.inertia (MulAction.stabilizer G Q) →* (S ⧸ Q)ˣ :=
  LinearEquiv.det.comp (DistribMulAction.toModuleAut (S ⧸ Q) Q.Cotangent)

theorem tameCharacter_apply (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q)) :
    tameCharacter G Q τ = (DistribMulAction.toLinearEquiv (S ⧸ Q) Q.Cotangent τ).det := rfl

open Module

/-- (Rigidity, L2) Multiplicativity of `τ` propagates the order-two vanishing along the `Q`-adic
filtration: from `τ • x ≡ x mod Q ^ 2` on `Q`, one gets `τ • x ≡ x mod Q ^ (n + 2)` on `Q ^ (n+1)`. -/
theorem sub_mem_pow_of_sub_mem (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q))
    (h : ∀ x ∈ Q, τ • x - x ∈ Q ^ 2) (n : ℕ) {x : S} (hx : x ∈ Q ^ n) :
    τ • x - x ∈ Q ^ (n + 1) := by
  induction n generalizing x with
  | zero =>
    simp_all
    exact τ.prop x
  | succ n hind =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun x hx y hy ↦ ?_) fun x y hx hy ↦ ?_
      · rw [show τ • (x * y) - x * y = (τ • x - x) * τ • y + x * (τ • y - y)
          by rw [MulSemiringAction.smul_mul]; ring]
        refine Submodule.add_mem _ ?_ ?_
        · rw [add_right_comm, pow_add, pow_one]
          exact Submodule.mul_mem_mul (hind hx) (smul_mem_of_mem_stabilizer _ _ hy)
        · rw [show n + 1 + 1 = n + 2 by ring, pow_add]
          exact Submodule.mul_mem_mul hx (h _ hy)
      · rw [smul_add, add_sub_add_comm]
        exact Submodule.add_mem _ hx hy

/-- (Rigidity, L3) If `τ` is inertia, fixes every graded piece, and has order prime to the residue
characteristic, then `τ • x ≡ x` modulo every power of `Q`. Proof: `τ ^ m = id + m·δ + …` with
`δ = τ - id`; since `m` is a unit in `S ⧸ Q`, the bound on `δ` improves by one at each power. -/
theorem sub_mem_pow_of_coprime (Q : Ideal S) [Q.IsMaximal]
    (τ : Q.inertia (MulAction.stabilizer G Q))
    (hstep : ∀ ⦃n : ℕ⦄, ∀ x ∈ Q ^ n, τ • x - x ∈ Q ^ (n + 1))
    (hord : ↑(orderOf τ) ∉ Q) (n : ℕ) (x : S) :
    τ • x - x ∈ Q ^ n := by
  set δ := τ • x - x with δ_def
  induction n with
  | zero => simp
  | succ n hind =>
      have h₁ {k : ℕ} : (τ ^ k • δ) - δ ∈ Q ^ (n + 1) := by
        induction k with
        | zero => simp
        | succ k hind' =>
            have : τ ^ k • (τ • δ - δ) + (τ ^ k • δ - δ) = τ ^ k • τ • δ - δ := by
              calc
                _ = τ ^ k • τ • δ - τ ^ k • δ + (τ ^k • δ - δ) := by rw [smul_sub]
                _ = τ ^ k • τ • δ - δ := by ring
            rw [pow_succ τ, ← smul_smul, ← this]
            exact Ideal.add_mem _ (smul_mem_pow_of_mem_stabilizer _ _ (hstep _ hind)) hind'
      simp_rw [← Quotient.mk_eq_mk_iff_sub_mem] at h₁
      have h₂ : ∑ k ∈ Finset.range (orderOf τ), Ideal.Quotient.mk (Q ^ (n + 1)) (τ ^ k • δ) = 0 := by
        simp only [δ_def, smul_sub, smul_smul, ← pow_succ]
        rw [← map_sum, Finset.sum_range_sub (fun k ↦ τ ^ k • x), pow_orderOf_eq_one τ, pow_zero,
          sub_self, map_zero]
      simp_rw [h₁, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h₂
      rwa [IsUnit.mul_right_eq_zero, Quotient.eq_zero_iff_mem] at h₂
      exact Quotient.isUnit_mk_pow_of_notMem _ hord

variable [IsDedekindDomain S]

/-- The localization of a Dedekind domain at a nonzero maximal ideal is a discrete valuation ring.
A local instance so that `Ideal.finrank_cotangent_eq_one` applies to the cotangent line `Q ⧸ Q ^ 2`. -/
private instance (Q : Ideal S) [Q.IsMaximal] [NeZero Q] :
    IsDiscreteValuationRing (Localization.AtPrime Q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S (NeZero.ne Q) _

/-- In dimension one, the cotangent action of an inertia element is the homothety by its tame
character: `cotangentInertiaAction G Q τ = θ(τ) • id`. -/
theorem cotangentInertiaAction_apply_eq_smul (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    (τ : Q.inertia (MulAction.stabilizer G Q)) (v : Q.Cotangent) :
    τ • v = (tameCharacter G Q τ).val • v := by
  let := Ideal.Quotient.field Q
  rw [tameCharacter_apply, LinearEquiv.coe_det]
  exact LinearMap.apply_eq_det_smul_of_finrank_eq_one Q.finrank_cotangent_eq_one
    (DistribMulAction.toLinearEquiv (S ⧸ Q) Q.Cotangent τ) v

/-- (Rigidity, L1) If `θ(τ) = 1` then `τ` fixes the cotangent line `Q ⧸ Q ^ 2`: for `x ∈ Q`,
`τ • x ≡ x mod Q ^ 2`. Uses that `Q ⧸ Q ^ 2` is one-dimensional over the field `S ⧸ Q`, so
`det = 1` forces the action to be the identity. -/
theorem sub_mem_sq_of_tameCharacter_eq_one (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    (τ : Q.inertia (MulAction.stabilizer G Q)) (h : tameCharacter G Q τ = 1) {x : S} (hx : x ∈ Q) :
    τ • x - x ∈ Q ^ 2 := by
  let := Ideal.Quotient.field Q
  have : DistribMulAction.toLinearEquiv (S ⧸ Q) Q.Cotangent τ = 1 := by
    rw [← LinearEquiv.toLinearMap_inj, LinearEquiv.coe_toLinearMap_one,
      ← LinearMap.det_eq_one_iff_eq_id Q.finrank_cotangent_eq_one, ← LinearEquiv.coe_det,
      ← tameCharacter_apply, h, Units.val_one]
  simpa [DistribMulAction.toLinearEquiv_apply, MulAction.subgroup_smul_def,
    smul_toCotangent, toCotangent_eq] using LinearEquiv.congr_fun this (Q.toCotangent ⟨x, hx⟩)

/-- (Rigidity, L4) An inertia element acting trivially on `S` is trivial. Uses Krull's intersection
theorem (`⋂ₙ Q ^ n = ⊥`) to pass from "trivial modulo every power" to "trivial", and faithfulness
of the action to conclude `τ = 1`. -/
theorem eq_one_of_forall_sub_mem_pow [FaithfulSMul G S] (Q : Ideal S) [hQ : Q.IsMaximal]
    (τ : Q.inertia (MulAction.stabilizer G Q))
    (h : ∀ (n : ℕ) (x : S), τ • x - x ∈ Q ^ n) : τ = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := S) fun x ↦ ?_
  simpa [iInf_pow_eq_bot_of_isDomain _ hQ.ne_top, sub_eq_zero] using mem_iInf.mpr fun i ↦ h i x

/-- **Rigidity** (filtration-free): an inertia element of order prime to the residue
characteristic on which the tame character vanishes is trivial. -/
theorem eq_one_of_tameCharacter_eq_one [FaithfulSMul G S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    (τ : Q.inertia (MulAction.stabilizer G Q)) (hord : ↑(orderOf τ) ∉ Q)
    (h : tameCharacter G Q τ = 1) : τ = 1 := by
  apply eq_one_of_forall_sub_mem_pow
  apply sub_mem_pow_of_coprime
  apply sub_mem_pow_of_sub_mem
  · exact fun x a ↦ sub_mem_sq_of_tameCharacter_eq_one Q τ h a
  · exact hord

variable (G) in
theorem tameCharacter_injective [FaithfulSMul G S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    Function.Injective (tameCharacter G Q) := by
  refine (injective_iff_map_eq_one _).mpr fun τ hτ ↦ eq_one_of_tameCharacter_eq_one _ _ ?_ hτ
  contrapose! htame
  obtain ⟨q, hq⟩ := Nat.cast_dvd_cast (α := S) <| orderOf_dvd_natCard τ
  exact hq ▸ Ideal.mul_mem_right _ _ htame

attribute [local instance] Ideal.Quotient.field in
/-- **Frobenius equivariance**: conjugating an inertia element by an arithmetic Frobenius
raises the tame character to the `N 𝔭`-th power. (Conjugation lands back in inertia by
normality, via `MulAut.conjNormal`.) -/
theorem tameCharacter_conj (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    (σ : MulAction.stabilizer G Q) (hσ : IsArithFrobAt R σ Q)
    (τ : Q.inertia (MulAction.stabilizer G Q)) :
    tameCharacter G Q (MulAut.conjNormal σ τ) = tameCharacter G Q τ ^ Nat.card (R ⧸ Q.under R) := by
  suffices DistribSMul.toLinearMap (S ⧸ Q) Q.Cotangent (MulAut.conjNormal σ τ) =
      (σ • (tameCharacter G Q τ).val) • LinearMap.id by
    rw [Units.ext_iff, tameCharacter_apply, LinearEquiv.coe_det,
      DistribMulAction.coe_toLinearEquiv, congr_arg (LinearMap.det · ) this, hσ.smul_residue,
      LinearMap.det_smul, Q.finrank_cotangent_eq_one, pow_one, LinearMap.det_id, mul_one,
      Units.val_pow_eq_pow_val]
  ext v
  rw [DistribSMul.toLinearMap_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    show v = σ • (σ⁻¹ • v) by rw [smul_inv_smul], MulAction.subgroup_smul_def,
    MulAut.conjNormal_apply, ← smul_smul, inv_smul_smul, ← smul_smul,
    ← MulAction.subgroup_smul_def, cotangentInertiaAction_apply_eq_smul, stabilizer_smul_smul]

/-- **Tame inertia is cyclic**: if the order of the inertia group is prime to the residue
characteristic (tame ramification), the inertia group is cyclic. -/
theorem isCyclic_inertia (Q : Ideal S) [Q.IsMaximal] [NeZero Q] [Finite (S ⧸ Q)] [FaithfulSMul G S]
    (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    IsCyclic (Q.inertia (MulAction.stabilizer G Q)) :=
  isCyclic_of_injective _ (tameCharacter_injective G Q htame)

/-- **Abelian tame ramification**: for an abelian action, the order of the inertia group
(the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one (Q : Ideal S) [Q.IsMaximal] [NeZero Q] [FaithfulSMul G S]
    [Finite G] [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)] [IsMulCommutative G]
    (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    Nat.card (Q.inertia (MulAction.stabilizer G Q)) ∣ Nat.card (R ⧸ Q.under R) - 1 := by
  obtain ⟨τ, hτ⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp <| isCyclic_inertia Q htame
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant R G Q
  rw [← hτ, ← orderOf_injective _ (tameCharacter_injective G Q htame), ← Int.natCast_dvd_natCast,
    orderOf_dvd_iff_zpow_eq_one, Nat.cast_sub hσ.card_pos, Nat.cast_one, zpow_sub_one,
    zpow_natCast, ← tameCharacter_conj Q ⟨σ, hσ.mem_stabilizer⟩ hσ.of_coe τ,
    MulAut.conjNormal_apply_of_isMulCommutative, mul_inv_cancel]

end Ideal

end
