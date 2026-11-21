module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Relrank
public import Mathlib.LinearAlgebra.Dimension.Domain
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import SKW.PRed2Mathlib.CyclotomicField
public import SKW.PRed2Mathlib.KroneckerWeber
public import SKW.PRed2Mathlib.Subfield
public import SKW.Prereqs.OtherPR
public import SKW.Prereqs.Stickelberger

set_option linter.style.header false

@[expose] public section

/-!
# Prerequisites for the Kronecker-Weber theorem

This file gathers the results from the `SKW.Prereqs` files that are needed in
`SKW.KroneckerWeber.KroneckerWeber`. Those from `SKW.Prereqs.Stickelberger` stay there.
-/

-- From `SKW.Prereqs.AlgebraMisc`.
section

open Function nonZeroDivisors in
/-- The map of fraction fields induced by an injective `algebraMap A B` is `algebraMap K L`. -/
@[simp]
theorem IsFractionRing.map_algebraMap_apply {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    (hj : Injective (algebraMap A B)) (x : K) :
    map hj x = algebraMap K L x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext A⁰ <| RingHom.ext fun a ↦ by
    simp [map, ← IsScalarTower.algebraMap_apply]) x

/-- Analogue of `IsPrimitiveRoot.pow` for `orderOf`: if `orderOf x = a * b` then
`orderOf (x ^ a) = b`. -/
theorem orderOf_pow_of_orderOf_eq_mul {G : Type*} [Monoid G] {x : G} {a b : ℕ}
    (hn : 0 < orderOf x) (h : orderOf x = a * b) : orderOf (x ^ a) = b := by
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hn.ne')
  rw [orderOf_pow_of_dvd ha ⟨b, h⟩, h, Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero ha)]

/-- The group-theoretic heart of the tame Abhyankar lemma: a cyclic group that embeds into a product
`A × B` of finite groups has order dividing `Nat.lcm (Nat.card A) (Nat.card B)`. (A generator maps
  to
some `(a, b)` of order `lcm (orderOf a) (orderOf b)`, and each component order divides the
corresponding cardinality.) -/
theorem Subgroup.card_dvd_lcm_of_isCyclic_of_injective {G A B : Type*} [Group G] [Group A] [Group B]
    [IsCyclic G] {f : G →* A × B} (hf : Function.Injective f) :
    Nat.card G ∣ Nat.lcm (Nat.card A) (Nat.card B) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  rw [← Subgroup.card_top, ← (Subgroup.eq_top_iff' _).mpr hg, Nat.card_zpowers g,
    ← orderOf_injective f hf g, Prod.orderOf]
  exact Nat.lcm_dvd ((_root_.orderOf_dvd_natCard _).trans (Nat.dvd_lcm_left _ _))
      ((_root_.orderOf_dvd_natCard _).trans (Nat.dvd_lcm_right _ _))

/-- In a cyclic group, the lcm of the indices of two subgroups of trivial intersection is the order
of the group. -/
theorem Subgroup.lcm_index_eq_card_of_isCyclic_of_inf_eq_bot {G : Type*} [Group G] [IsCyclic G]
    {H₁ H₂ : Subgroup G} (h : H₁ ⊓ H₂ = ⊥) :
    Nat.lcm H₁.index H₂.index = Nat.card G :=
  dvd_antisymm (Nat.lcm_dvd H₁.index_dvd_card H₂.index_dvd_card) <|
    card_dvd_lcm_of_isCyclic_of_injective (f := (QuotientGroup.mk' H₁).prod (QuotientGroup.mk' H₂))
      (by rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod, QuotientGroup.ker_mk',
        QuotientGroup.ker_mk', h])

/-- `subgroupOf` distributes over `⊓` (the general case of `inf_subgroupOf_left`/`_right`); this is
`Subgroup.comap_inf` for the inclusion `C.subtype`. -/
@[to_additive /-- `addSubgroupOf` distributes over `⊓`; this is `AddSubgroup.comap_inf` for the
inclusion `C.subtype`. -/]
theorem Subgroup.subgroupOf_inf {G : Type*} [Group G] (A B C : Subgroup G) :
    (A ⊓ B).subgroupOf C = A.subgroupOf C ⊓ B.subgroupOf C :=
  Subgroup.comap_inf A B C.subtype

/-- `A.subgroupOf B` and `B.subgroupOf A` are isomorphic (both realize `A ⊓ B`). Mathlib only has
`subgroupOfEquivOfLe`; this composes two copies of it through `A ⊓ B`. -/
@[to_additive /-- `A.addSubgroupOf B` and `B.addSubgroupOf A` are isomorphic (both realize
  `A ⊓ B`). -/]
def Subgroup.subgroupOfEquivComm {G : Type*} [Group G] (A B : Subgroup G) :
    A.subgroupOf B ≃* B.subgroupOf A :=
  ((MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right A B).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)).trans
    ((MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_left B A).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_left)).symm

/-- Division-free companion to `Subgroup.card_mul_index`: `d` is the index of `H` iff
`Nat.card H * d = Nat.card G`. -/
@[to_additive AddSubgroup.index_eq_iff_card_mul_eq_card /-- Division-free companion to
`AddSubgroup.card_mul_index`: `d` is the index of `H` iff `Nat.card H * d = Nat.card G`. -/]
theorem Subgroup.index_eq_iff_card_mul_eq_card {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    {d : ℕ} : H.index = d ↔ Nat.card H * d = Nat.card G :=
  ⟨fun h ↦ h ▸ H.card_mul_index,
    fun h ↦ Nat.eq_of_mul_eq_mul_left Nat.card_pos (H.card_mul_index.trans h.symm)⟩

@[simp]
theorem MulAut.conjNormal_apply_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G]
    {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    conjNormal g h = h := by
  rw [Subtype.ext_iff, conjNormal_apply, mul_comm', inv_mul_cancel_left]

section
variable {G R : Type*} [CommGroup G] [Finite G] [CommRing R] [IsDomain R]

instance (φ : G →* Rˣ) : IsCyclic (G ⧸ φ.ker) :=
  haveI : Finite φ.range := Finite.Set.finite_range _
  isCyclic_of_injective (QuotientGroup.quotientKerEquivRange φ).toMonoidHom (MulEquiv.injective _)

/-- The order of a character `φ : G →* Rˣ` (`R` a domain) equals the cardinality of the quotient of
`G` by its kernel (equivalently, of its cyclic image). -/
theorem MonoidHom.card_quotient_ker_eq_orderOf (φ : G →* Rˣ) :
    Nat.card (G ⧸ φ.ker) = orderOf φ := by
  have : Finite φ.range := Finite.Set.finite_range _
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, ← IsCyclic.exponent_eq_card]
  refine dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one ?_)
    (orderOf_dvd_iff_pow_eq_one.mpr ?_)
  · rintro ⟨_, ⟨g, rfl⟩⟩
    simp [Subtype.ext_iff, ← MonoidHom.pow_apply]
  · ext g
    simpa [Subtype.ext_iff, Units.ext_iff] using
      Monoid.pow_exponent_eq_one (G := φ.range) ⟨φ g, ⟨g, rfl⟩⟩
end

section AssociatesCount
variable {α β : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
  [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]
  [CommMonoidWithZero β] [UniqueFactorizationMonoid β]
  [DecidableEq (Associates β)] [∀ p : Associates β, Decidable (Irreducible p)]

namespace Associates
end Associates
end AssociatesCount

end

-- From `SKW.Prereqs.LinearAlgebra`.
section
open Module

theorem finrank_eq_of_equiv_equiv {R R' M M₁ : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Semiring R'] [AddCommMonoid M₁] [Module R' M₁] (i : R → R') (j : M ≃+ M₁)
    (hi : Function.Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.finrank R M = Module.finrank R' M₁ := by
  simpa using! congr_arg Cardinal.toNat <| lift_rank_eq_of_equiv_equiv i j hi hc

@[simp]
theorem DistribMulAction.coe_toLinearEquiv (R : Type*) {S : Type*} (M : Type*) [Semiring R]
    [AddCommMonoid M] [Module R M] [Group S] [DistribMulAction S M] [SMulCommClass S R M] (s : S) :
    (DistribMulAction.toLinearEquiv R M s : M →ₗ[R] M) = DistribSMul.toLinearMap R M s := rfl

end

-- From `SKW.Prereqs.NumberField`.
section

instance NumberField.sup {E F : Type*} [Field E] [Field F] [Algebra E F] (K L : IntermediateField E
  F)
    [NumberField K] [NumberField L] :
    NumberField ↑(K ⊔ L) :=
  haveI : CharZero E := (algebraMap E K).charZero
  { to_charZero := IntermediateField.charZero (K ⊔ L)
    to_finiteDimensional := by
      have : FiniteDimensional ℚ E := Module.Finite.left ℚ E K
      have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
      have : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
      exact FiniteDimensional.trans ℚ E _ }
open scoped NumberField

namespace NumberField.RingOfIntegers
variable {K L : Type*} [Field K] [Field L]

/-- The `ℤ`-algebra isomorphism `(𝓞 K) ≃ₐ[ℤ] (𝓞 L)` given by restricting a ring isomorphism
  `e : K ≃+* L` to `𝓞 K`. Unlike `RingOfIntegers.mapAlgEquiv`, whose base is `𝓞 k`, this has base
  `ℤ`, which is convenient when the natural common base of `K` and `L` is `ℚ` (as `𝓞 ℚ` is only
  isomorphic to, not equal to, `ℤ`). -/
def mapIntAlgEquiv (e : K ≃+* L) : (𝓞 K) ≃ₐ[ℤ] (𝓞 L) := (mapRingEquiv e).toIntAlgEquiv
end NumberField.RingOfIntegers

namespace NumberField
open InfinitePlace
variable {K : Type*} [Field K] [Algebra ℚ K] [IsGalois ℚ K]

theorem InfinitePlace.isReal_of_isGalois {w : InfinitePlace K} (hw : w.IsReal)
    (w' : InfinitePlace K) :
    w'.IsReal := by
  obtain ⟨σ, rfl⟩ : ∃ σ, σ • w = w' := exists_smul_eq_of_comap_eq (k := ℚ) (Subsingleton.elim _ _)
  exact isReal_smul_iff.mpr hw

theorem isTotallyComplex_iff_exists_isComplex [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ∃ w : InfinitePlace K, w.IsComplex := by
  refine ⟨fun h ↦ ⟨Classical.arbitrary _, h.isComplex _⟩, fun ⟨w, hw⟩ ↦ ⟨fun w' ↦ ?_⟩⟩
  exact not_isReal_iff_isComplex.mp fun h ↦ not_isReal_iff_isComplex.mpr hw (isReal_of_isGalois h w)

theorem isTotallyComplex_iff_not_isTotallyReal [Nonempty (InfinitePlace K)] :
    IsTotallyComplex K ↔ ¬ IsTotallyReal K := by
  simp_rw [isTotallyComplex_iff_exists_isComplex, isTotallyReal_iff, not_forall,
    not_isReal_iff_isComplex]

theorem isTotallyReal_iff_not_isTotallyComplex [Nonempty (InfinitePlace K)] :
    IsTotallyReal K ↔ ¬ IsTotallyComplex K := by
  rw [isTotallyComplex_iff_not_isTotallyReal, not_not]
end NumberField

end

-- From `SKW.Prereqs.Torsion`.
section

/-- If `a` and `b` are coprime, then `g` lies in the subgroup generated by `g ^ a` and `g ^ b`
(a special case of `Subgroup.zpowers_zpow_sup`, since `Nat.gcd a b = 1`). -/
theorem mem_sup_zpowers_pow_of_coprime {G : Type*} [Group G] {a b : ℕ}
    (h : Nat.Coprime a b) (g : G) :
    g ∈ Subgroup.zpowers (g ^ a) ⊔ Subgroup.zpowers (g ^ b) := by
  rw [← zpow_natCast g a, ← zpow_natCast g b, Subgroup.zpowers_zpow_sup,
    Int.gcd_natCast_natCast, h.gcd_eq_one, Nat.cast_one, zpow_one]
  exact Subgroup.mem_zpowers g

namespace CommGroup
variable {G : Type*} [CommGroup G]

/-- Auxiliary form of `mem_iSup_primaryComponent_primeFactors`, with `orderOf x` abstracted as `n`,
so that the proof can recurse on the prime-power factorization of `n`. -/
theorem mem_iSup_primaryComponent_primeFactors_aux {n : ℕ} {x : G} (hn : 0 < n) (hx : orderOf x =
  n) :
    x ∈ ⨆ q ∈ n.primeFactors, primaryComponent G q := by
  induction n using Nat.recOnPrimePow generalizing x with
  | zero =>
      exact False.elim <| Nat.not_succ_le_zero 0 hn
  | one => simpa using hx
  | prime_pow_mul m p k hp hpm hk h_ind =>
      have : Fact p.Prime := ⟨hp⟩
      have hm : 0 < m := by
        contrapose! hn
        simp_all
      have hcop : m.Coprime (p ^ k) := by
        rw [Nat.coprime_pow_right_iff hk, Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
      rw [hcop.symm.primeFactors_mul, Nat.primeFactors_prime_pow (ne_of_gt hk) hp,
        Finset.singleton_union, Finset.iSup_insert]
      refine mem_of_le_of_mem (sup_le_sup ?_ ?_) (mem_sup_zpowers_pow_of_coprime hcop x)
      · refine Subgroup.zpowers_le.mpr ?_
        rw [CommGroup.mem_primaryComponent_iff_orderOf,
          orderOf_pow_of_orderOf_eq_mul (by linarith) (by rwa [mul_comm])]
        exact ⟨k, rfl⟩
      · refine Subgroup.zpowers_le.mpr <| h_ind hm ?_
        rw [orderOf_pow_of_orderOf_eq_mul (by linarith) hx]

/-- A finite-order element lies in the join of the `p`-primary components, for `p` ranging over the
primes dividing its order. -/
theorem mem_iSup_primaryComponent_primeFactors {x : G} (hx : IsOfFinOrder x) :
    x ∈ ⨆ q ∈ (orderOf x).primeFactors, primaryComponent G q :=
  mem_iSup_primaryComponent_primeFactors_aux hx.orderOf_pos rfl

/-- Every element of a torsion commutative group lies in the join of its `p`-primary components. -/
theorem mem_iSup_primaryComponent (hG : IsMulTorsion G) (g : G) :
    g ∈ ⨆ p : Nat.Primes, primaryComponent G p := by
  refine mem_of_le_of_mem ?_ <| mem_iSup_primaryComponent_primeFactors (hG g)
  rw [show ⨆ p : Nat.Primes, primaryComponent G p = ⨆ p ∈ {n | Nat.Prime n}, primaryComponent G p
    from iSup_subtype]
  exact biSup_mono fun h hp ↦ (Nat.mem_primeFactors.mp hp).1

/-- In a torsion commutative group, the primary components generate the whole group. -/
theorem iSup_primaryComponent_eq_top (hG : IsMulTorsion G) :
    ⨆ p : Nat.Primes, primaryComponent G p = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ mem_iSup_primaryComponent hG g

/-- In a torsion commutative group, the elements of prime power order generate the whole group. -/
theorem closure_isPrimePow_orderOf_eq_top (hG : IsMulTorsion G) :
    Subgroup.closure {x : G | IsPrimePow (orderOf x)} = ⊤ := by
  rw [eq_top_iff, ← iSup_primaryComponent_eq_top hG,  iSup_le_iff]
  intro p x hx
  have : Fact p.val.Prime := ⟨p.prop⟩
  obtain ⟨k, hx'⟩ := mem_primaryComponent_iff_orderOf.mp hx
  by_cases hk : 0 < k
  · exact Subgroup.mem_closure_of_mem ⟨p, k, Nat.prime_iff.mp p.prop, hk, hx'.symm⟩
  · simp_all
end CommGroup

end

-- From `SKW.Prereqs.CMField`.
section
open NumberField IsCMField Units

section Units

namespace NumberField.IsCMField
variable {K : Type*} [Field K]

theorem exists_torsion_realunits_pow_indexRealUnits_eq_mul (u : (𝓞 K)ˣ) :
    ∃ ζ : Units.torsion K, ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧ u ^ indexRealUnits K = ζ * v := by
  obtain ⟨⟨v, hv⟩, ζ,
    h⟩ := Subgroup.mem_sup'.mp <| Subgroup.pow_index_mem (realUnits K ⊔ torsion K) u
  exact ⟨ζ, v, hv, by rwa [eq_comm, mul_comm]⟩
variable [CharZero K] [IsCMField K] [NumberField K]

/-- The `Units.val` of `unitsComplexConj` is `ringOfIntegersComplexConj` of the `Units.val`. Not a
`simp` lemma: `simp` rewrites the left-hand side further, through `Units.coe_mapEquiv`. -/
theorem coe_unitsComplexConj {K : Type*} [Field K] [CharZero K] [IsCMField K]
    [Algebra.IsIntegral ℚ K] (u : (𝓞 K)ˣ) :
    (unitsComplexConj K u).val = ringOfIntegersComplexConj K u.val := rfl
end NumberField.IsCMField
end Units

section RootsOfUnity

/-- A complex-conjugation-type automorphism sends a root of unity to its inverse. -/
theorem NumberField.ComplexEmbedding.IsConj.eq_inv_of_pow_eq_one {K : Type*} [Field K]
    {k : Type*} [Field k] [Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)}
    (hσ : IsConj φ σ) {ζ : K} {n : ℕ} [NeZero n] (hζ : ζ ^ n = 1) :
    σ ζ = ζ⁻¹ := by
  apply φ.injective
  rw [IsConj.eq hσ, RCLike.star_def, ← Complex.inv_eq_conj, map_inv₀]
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) (NeZero.ne n)

/-- A complex-conjugation-type automorphism sends a primitive root of unity to its inverse. -/
theorem NumberField.ComplexEmbedding.IsConj.eq_inv_of_isPrimitiveRoot {K : Type*} [Field K]
    {k : Type*} [Field k] [Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)}
    (hσ : IsConj φ σ) {ζ : K} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    σ ζ = ζ⁻¹ :=
  hσ.eq_inv_of_pow_eq_one hζ.pow_eq_one

/-- Complex conjugation of a CM field sends a primitive root of unity to its inverse. This is the
version of `NumberField.IsCMField.complexConj_torsion` for an arbitrary primitive root. -/
theorem NumberField.IsCMField.complexConj_eq_inv_of_isPrimitiveRoot {K : Type*} [Field K]
    [NumberField K] [IsCMField K] {ζ : K} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) :
    complexConj K ζ = ζ⁻¹ :=
  (isConj_complexConj K
    (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))).eq_inv_of_isPrimitiveRoot hζ
end RootsOfUnity

section CMGaloisGroup

namespace NumberField.IsCMField

noncomputable section
variable (K : Type*) [Field K] [CharZero K] [Algebra.IsIntegral ℚ K] [IsCMField K]
local notation3 "K⁺" => maximalRealSubfield K

/-- Complex conjugation of the CM field `K`, as an element of `Gal(K/ℚ)`. -/
noncomputable def ratComplexConj : Gal(K/ℚ) :=
  (complexConj K).restrictScalars ℚ

@[simp]
theorem ratComplexConj_apply (x : K) : ratComplexConj K x = complexConj K x := rfl
variable {K}
variable (K)

omit [Algebra.IsIntegral ℚ K] in
/-- A CM field has twice the degree of its maximal real subfield. -/
theorem finrank_eq_two_mul :
    Module.finrank ℚ K = 2 * Module.finrank ℚ K⁺ := by
  rw [← Module.finrank_mul_finrank ℚ K⁺ K, Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K,
    mul_comm]

open IntermediateField in
/-- The subfield of a CM field fixed by complex conjugation is its maximal real subfield. -/
theorem toSubfield_fixedField_ratComplexConj :
    (fixedField (Subgroup.zpowers (ratComplexConj K))).toSubfield = maximalRealSubfield K := by
  ext x
  rw [Subfield.mem_mk, Subring.mem_mk, Subalgebra.mem_toSubsemiring, mem_toSubalgebra,
    mem_fixedField_iff, Subgroup.forall_mem_zpowers, ← complexConj_eq_self_iff]
  exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := ratComplexConj K)).trans <| by simp

open IntermediateField in
/-- The subfield of a CM field fixed by complex conjugation is totally real. -/
instance isTotallyReal_fixedField_ratComplexConj :
    IsTotallyReal (fixedField (Subgroup.zpowers (ratComplexConj K))) := by
  change IsTotallyReal (fixedField (Subgroup.zpowers (ratComplexConj K))).toSubfield
  rw [toSubfield_fixedField_ratComplexConj]
  infer_instance
end

section Subfields
variable {K L : Type*} [Field K] [Field L] [CharZero K] [Algebra.IsIntegral ℚ K] [CharZero L]
  [Algebra.IsIntegral ℚ L] [IsCMField K] [IsCMField L] [Algebra K L]
end Subfields
end NumberField.IsCMField
end CMGaloisGroup

end

-- From `SKW.Prereqs.Ideals`.
section
open NumberField

@[simps]
def Ideal.mapEquiv {R S F : Type*} [CommSemiring R] [CommSemiring S] [EquivLike F R S]
    [RingHomClass F R S] (e : F) : Ideal R ≃+* Ideal S where
  toFun := Ideal.map e
  invFun := Ideal.comap e
  __ := Ideal.mapHom e
  left_inv _ := by simpa using comap_map_of_bijective _ (EquivLike.bijective e)
  right_inv _ := by simpa using Ideal.map_comap_of_surjective _ (EquivLike.surjective e) _

theorem Ideal.mapEquiv_eq_bot_iff {R S F : Type*} [CommSemiring R] [CommSemiring S]
    [EquivLike F R S] [RingHomClass F R S] (e : F) (I : Ideal R) :
    I.mapEquiv e = ⊥ ↔ I = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rwa [← RingEquiv.eq_symm_apply, mapEquiv_symm_apply,
    comap_bot_of_injective _ (EquivLike.injective e)] at h

theorem IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv_apply_asIdeal {R S : Type*}
    [CommRing R] [CommRing S] (f : R ≃+* S) (v : HeightOneSpectrum R) :
    (equivOfRingEquiv f v).asIdeal = v.asIdeal.map f := by
  simp only [equivOfRingEquiv_apply, ← RingEquiv.toRingHom_eq_coe, comap_asIdeal]
  exact Ideal.comap_symm f

/-- Every height one prime of `R` lies below a height one prime of `S`. -/
theorem IsDedekindDomain.HeightOneSpectrum.under_surjective {R S : Type*} [CommRing R]
    [CommRing S] [IsDedekindDomain R] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S] :
    Function.Surjective
      (HeightOneSpectrum.under R : HeightOneSpectrum S → HeightOneSpectrum R) := by
  intro v
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
    HeightOneSpectrum.ext <| by simp [under_asIdeal, (Ideal.liesOver_iff _ _).mp hQ']⟩

/-- For a maximal ideal `I`, `R ⧸ I` is already its own fraction field, so the canonical map to
the residue field `κ(I) = ResidueField R_I` of the localization is an isomorphism. -/
noncomputable def Ideal.residueFieldEquiv {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    R ⧸ I ≃+* I.ResidueField :=
  RingEquiv.ofBijective _ I.bijective_algebraMap_quotient_residueField

@[simp]
theorem Ideal.residueFieldEquiv_mk {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] (x : R) :
    I.residueFieldEquiv (Ideal.Quotient.mk I x) = algebraMap R I.ResidueField x := rfl

open Pointwise in
theorem Ideal.pointwise_smul_def' {M R : Type*} [Group M] [CommSemiring R] [MulSemiringAction M R]
  {a : M}
    (S : Ideal R) :
    a • S = mapEquiv (MulSemiringAction.toRingEquiv M R a) S := rfl

-- Replace Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul?
-- TODO(SKW): the statement is already unprimed, but the proof bridges back to the primed index
-- because `emultiplicity_map_eq_ramificationIdx'_mul` has no unprimed version upstream. Once it
-- does, the `rw` below goes, and `ramificationIdx'_ne_zero` becomes
-- `ramificationIdx_pos_of_isDedekindDomain'`.
theorem Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul' {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} (I : Ideal R) (hv : v ≠ ⊥) [w.IsPrime]
    (hw : w ≠ ⊥) [w.LiesOver v] :
    emultiplicity w (map (algebraMap R S) I) = w.ramificationIdx R * emultiplicity v I := by
  have := isPrime_of_liesOver w v
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v w hv]
  by_cases hI : I = ⊥
  · rw [hI, map_bot, ← zero_eq_bot, ← zero_eq_bot, emultiplicity_zero_right,
    emultiplicity_zero_right, ENat.mul_top]
    simp only [ne_eq, Nat.cast_eq_zero]
    apply ramificationIdx'_ne_zero (map_ne_bot_of_ne_bot hv) ‹_›
    rw [map_le_iff_le_comap, over_def w v]
  · exact emultiplicity_map_eq_ramificationIdx'_mul hI
      (irreducible_iff_prime.mpr ((prime_iff_isPrime hv).mpr ‹_›))
      (irreducible_iff_prime.mpr ((prime_iff_isPrime hw).mpr ‹_›)) hw

theorem Ideal.IsDedekindDomain.multiplicity_map_eq_ramificationIdx_mul {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} (I : Ideal R) (hv : v ≠ ⊥) [w.IsPrime]
    (hw : w ≠ ⊥) [w.LiesOver v] :
    multiplicity w (map (algebraMap R S) I) = w.ramificationIdx R * multiplicity v I := by
  by_cases hI : I = ⊥
  · simp [hI]
  have := isPrime_of_liesOver w v
  have h := emultiplicity_map_eq_ramificationIdx_mul' I hv hw
  rw [(FiniteMultiplicity.of_not_isUnit (isUnit_iff.not.mpr IsPrime.ne_top')
      (map_ne_bot_of_ne_bot hI)).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_not_isUnit (isUnit_iff.not.mpr IsPrime.ne_top')
      hI).emultiplicity_eq_multiplicity] at h
  exact mod_cast h

theorem Ideal.IsDedekindDomain.ramificationIdx_mul_multiplicity_under_eq {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R]
    [FaithfulSMul R S] [Algebra.IsIntegral R S] {w : Ideal S} [w.IsPrime] (hw : w ≠ ⊥)
    {I : Ideal R} :
    w.ramificationIdx R * multiplicity (under R w) I = multiplicity w (map (algebraMap R S) I) :=
  (multiplicity_map_eq_ramificationIdx_mul I (under_ne_bot R hw) hw).symm

open Pointwise in
@[simp]
theorem Ideal.smul_eq_bot_iff {M : Type*} {R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]
    {m : M} {I : Ideal R} : m • I = ⊥ ↔ I = ⊥ := by
  rw [smul_eq_iff_eq_inv_smul, smul_bot]

open Pointwise in
/-- An element of the stabilizer of `I` preserves `I`. -/
theorem Ideal.smul_mem_of_mem_stabilizer {M R : Type*} [Group M] [CommRing R] [MulSemiringAction M
  R]
    (I : Ideal R) (σ : MulAction.stabilizer M I) {x : R} (hx : x ∈ I) : σ • x ∈ I := by
  nth_rewrite 1 [← MulAction.mem_stabilizer_iff.mp σ.prop]
  exact smul_mem_pointwise_smul σ x I hx

open Pointwise in
/-- An element of the stabilizer of `I` preserves `I ^ k`. -/
theorem Ideal.smul_mem_pow_of_mem_stabilizer {M R : Type*} [Group M] [CommRing R]
    [MulSemiringAction M R] (I : Ideal R) (σ : MulAction.stabilizer M I) {x : R} {k : ℕ}
    (hx : x ∈ I ^ k) : σ • x ∈ I ^ k := by
  nth_rewrite 1 [← MulAction.mem_stabilizer_iff.mp σ.prop, ← smul_pow']
  exact smul_mem_pointwise_smul σ x _ hx

/-- Ideal version of `AddSubgroup.subgroupOf_inertia`: the inertia of `I` in a subgroup `H ≤ G` is
the restriction to `H` of the inertia in `G`. -/
theorem Ideal.subgroupOf_inertia {R : Type*} [Ring R] (I : Ideal R) {G : Type*} [Group G]
    [MulAction G R] (H : Subgroup G) : (I.inertia G).subgroupOf H = I.inertia H :=
  AddSubgroup.subgroupOf_inertia I.toAddSubgroup H

namespace Ideal
variable {R : Type*} (A : Type*) (B : Type*) [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (p : Ideal R)
end Ideal

namespace Ideal

section dvd_finrank
variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
  (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Flat A B]
  [FaithfulSMul A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B]

include G in
theorem ramificationIdxIn_dvd_finrank : p.ramificationIdxIn B ∣ Module.finrank A B := by
  rw [← IsGaloisGroup.card_eq_finrank' G,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
end dvd_finrank
end Ideal

end

-- From `SKW.Prereqs.Cotangent`.
section
open Module
open IsLocalization.AtPrime IsLocalRing
variable {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal]
local notation3 "R_I" => Localization.AtPrime I

/-- The natural map `I ⧸ I ^ 2 → 𝔪 ⧸ 𝔪 ^ 2` induced by `algebraMap R R_I`, landing directly in
`CotangentSpace R_I`, built as `Submodule.mapQ` of `algebraMap R R_I` corestricted to
`maximalIdeal R_I` (`to_map_mem_maximal_iff`). It is `R`-linear (the `R`-action on the target
factors through `algebraMap`), with apply lemma
`cotangentMap (toCotangent x) = toCotangent ⟨algebraMap x, _⟩`. -/
noncomputable def Ideal.cotangentMap : I.Cotangent →ₗ[R] CotangentSpace R_I :=
  let g := Submodule.mapQ (I • ⊤) (maximalIdeal R_I • ⊤)
    ((algebraMap R R_I).toSemilinearMap.restrict
      (fun x hx ↦ (to_map_mem_maximal_iff R_I I x).mpr hx)) (fun x hx ↦ by
        refine Submodule.smul_induction_on hx (fun a ha _ _ ↦ ?_) (fun _ _ ↦ add_mem)
        rw [Submodule.mem_comap, map_smulₛₗ]
        exact Submodule.smul_mem_smul ((to_map_mem_maximal_iff R_I I a).mpr ha) Submodule.mem_top)
  { toAddHom := g.toAddHom
    map_smul' := fun r c ↦ (map_smulₛₗ g r c).trans (algebraMap_smul _ r (g c)) }

theorem cotangentMap_mk_smul (r : R) (x : I.Cotangent) :
    I.cotangentMap (Ideal.Quotient.mk I r • x) = r • I.cotangentMap x :=
  LinearMap.map_smul I.cotangentMap r x

@[simp]
theorem Ideal.cotangentMap_toCotangent (x : I) :
    I.cotangentMap (I.toCotangent x)
      = (maximalIdeal R_I).toCotangent
        ⟨algebraMap R R_I x, (to_map_mem_maximal_iff R_I I x).mpr x.2⟩ := rfl

/-- **Injectivity** (kernel `I ^ 2`): `cotangentMap (toCotangent x) = 0 ↔ algebraMap x ∈ 𝔪 ^ 2 ↔
x ∈ I ^ 2` (`under_maximalIdeal_pow`). -/
theorem Ideal.cotangentMap_injective : Function.Injective I.cotangentMap := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective a
  rw [cotangentMap_toCotangent, toCotangent_eq_zero] at ha
  rwa [toCotangent_eq_zero, ← under_maximalIdeal_pow I R_I 2, mem_under]

/-- **Surjectivity**: a class in `𝔪 ⧸ 𝔪 ^ 2` is `toCotangent ⟨y, _⟩` with `y ∈ 𝔪`; pulling the
class of `y` back along `R ⧸ I ^ 2 ≃ Rₚ ⧸ 𝔪 ^ 2` (`equivQuotMaximalIdealPow`) gives `a ∈ R` with
`algebraMap a ≡ y` mod `𝔪 ^ 2` (so the same cotangent class) and `algebraMap a ∈ 𝔪` (so `a ∈ I`). -/
theorem Ideal.cotangentMap_surjective :
    Function.Surjective I.cotangentMap := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := (maximalIdeal R_I).toCotangent_surjective z
  obtain ⟨a, ha⟩ := Quotient.mk_surjective ((equivQuotMaximalIdealPow I R_I 2).symm y)
  replace ha : Quotient.mk (maximalIdeal R_I ^ 2) (algebraMap R R_I a)
      = Quotient.mk (maximalIdeal R_I ^ 2) y := by
    rw [← equivQuotMaximalIdealPow_apply_mk I R_I 2 a, ha, AlgEquiv.apply_symm_apply]
  refine ⟨I.toCotangent ⟨a, ?_⟩, ?_⟩
  · rw [← to_map_mem_maximal_iff R_I I, ← mk_mem_cotangentIdeal, ha]
    exact mk_mem_cotangentIdeal.mpr hy
  · simpa [cotangentMap_toCotangent, toCotangent_eq, ← Quotient.mk_eq_mk_iff_sub_mem]

/-- The cotangent line `I ⧸ I ^ 2` is intrinsic to the local ring at `I`: it is additively
isomorphic to the cotangent space of `R_I`, as `AddEquiv.ofBijective` of `cotangentMap`. -/
noncomputable def Ideal.cotangentEquivCotangentSpace : I.Cotangent ≃+ CotangentSpace R_I :=
  AddEquiv.ofBijective I.cotangentMap.toAddMonoidHom
    ⟨I.cotangentMap_injective, I.cotangentMap_surjective⟩

@[simp]
theorem Ideal.cotangentEquivCotangentSpace_apply (z : I.Cotangent) :
    I.cotangentEquivCotangentSpace z = I.cotangentMap z := rfl

/-- `Ideal.cotangentEquivCotangentSpace` is semilinear over the residue-field identification
`Ideal.residueFieldEquiv : R ⧸ I ≃+* κ(I)`: `cotangentMap` is `R`-linear, and `R` acts on
`CotangentSpace R_I` through `κ(I)`. -/
theorem Ideal.cotangentEquivCotangentSpace_smul (c : R ⧸ I) (x : I.Cotangent) :
    I.cotangentEquivCotangentSpace (c • x)
      = I.residueFieldEquiv c • I.cotangentEquivCotangentSpace x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [cotangentEquivCotangentSpace_apply, cotangentMap_mk_smul, residueFieldEquiv_mk,
    IsScalarTower.algebraMap_apply R R_I I.ResidueField, algebraMap_smul]

/-- If the localization `R_I` of `R` at a maximal ideal `I` is a discrete valuation ring, then the
cotangent space `I ⧸ I ^ 2` is a one-dimensional vector space over the residue field `R ⧸ I` (its
cotangent line). This is a local statement: only the local ring at `I` matters. -/
theorem Ideal.finrank_cotangent_eq_one [IsDomain R] [IsDiscreteValuationRing R_I] :
    finrank (R ⧸ I) I.Cotangent = 1 := by
  rw [finrank_eq_of_equiv_equiv I.residueFieldEquiv I.cotangentEquivCotangentSpace
    I.residueFieldEquiv.bijective I.cotangentEquivCotangentSpace_smul]
  exact IsLocalRing.finrank_CotangentSpace_eq_one R_I

section Action

namespace Ideal
open scoped Pointwise
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [Group M] [MulSemiringAction M R]

/-- The stabilizer of `I` acts on the cotangent space `I.Cotangent` -/
instance : SMul (MulAction.stabilizer M I) I.Cotangent where
  smul m v :=
    Submodule.mapQ (I • ⊤) (I • ⊤)
      ((MulSemiringAction.toRingHom M R (m : M)).toSemilinearMap.restrict
        (fun x hx ↦ Ideal.smul_mem_of_mem_stabilizer I m hx))
        (fun x hx ↦ by
          rw [Submodule.mem_smul_top_iff, smul_eq_mul, ← pow_two] at hx
          simp only [Submodule.mem_comap, Submodule.mem_smul_top_iff,
            smul_eq_mul, ← pow_two]
          exact Ideal.smul_mem_pow_of_mem_stabilizer I m hx) v

theorem smul_toCotangent (m : MulAction.stabilizer M I) (x : I) :
    m • I.toCotangent x = I.toCotangent ⟨m • x, I.smul_mem_of_mem_stabilizer m x.prop⟩ := rfl

/-- The stabilizer of `I` acts additively on the cotangent space `I.Cotangent` -/
instance : DistribMulAction (MulAction.stabilizer M I) I.Cotangent where
  mul_smul m n v := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    simp [smul_toCotangent, smul_smul]
  one_smul v := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    simp [smul_toCotangent]
  smul_zero m := by
    rw [← LinearMap.map_zero I.toCotangent, smul_toCotangent, toCotangent_eq]
    simp
  smul_add m v w := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective w
    simp [← map_add, smul_toCotangent]

/-- The stabilizer of `I` acts on the residue ring `R ⧸ I`. -/
instance : SMul (MulAction.stabilizer M I) (R ⧸ I) where
  smul m x := Ideal.quotientMap I (MulSemiringAction.toRingHom M R (m : M))
    (fun _ hy ↦ Ideal.smul_mem_of_mem_stabilizer I m hy) x

theorem stabilizer_smul_mk (m : MulAction.stabilizer M I) (x : R) :
    m • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (m • x) := rfl

/-- The stabilizer of `I` acts on the residue ring `R ⧸ I` by ring automorphisms. -/
instance : MulSemiringAction (MulAction.stabilizer M I) (R ⧸ I) where
  one_smul q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [stabilizer_smul_mk]
  mul_smul m n q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [stabilizer_smul_mk, mul_smul]
  smul_zero m := by
    rw [← map_zero (Ideal.Quotient.mk I), stabilizer_smul_mk, smul_zero]
  smul_add m q r := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [stabilizer_smul_mk, ← map_add, smul_add]
  smul_one m := by rw [← map_one (Ideal.Quotient.mk I), stabilizer_smul_mk, smul_one]
  smul_mul m q r := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [stabilizer_smul_mk, ← map_mul]

/-- The stabilizer action on `R ⧸ I` is compatible with the `R`-algebra structure:
`g • (r • c) = (g • r) • (g • c)`. -/
instance : SMulDistribClass (MulAction.stabilizer M I) R (R ⧸ I) where
  smul_distrib_smul g r s := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective s
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, stabilizer_smul_mk, ← map_mul]

/-- The cotangent action is semilinear over the residue action. -/
theorem stabilizer_smul_smul (g : MulAction.stabilizer M I) (c : R ⧸ I) (v : I.Cotangent) :
    g • (c • v) = (g • c) • (g • v) := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [stabilizer_smul_mk, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, ← map_smul,
    smul_toCotangent, smul_toCotangent, algebraMap_smul, ← map_smul, toCotangent_eq]
  simp

/-- An inertia element acts trivially on the residue ring `R ⧸ I`. -/
theorem inertia_smul_residue (τ : I.inertia (MulAction.stabilizer M I)) (c : R ⧸ I) :
    (τ : MulAction.stabilizer M I) • c = c := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [stabilizer_smul_mk, Ideal.Quotient.eq]
  exact τ.prop x

/-- The inertia action on the cotangent space is `R ⧸ I`-linear: it commutes with the residue
scalar action. This makes `DistribMulAction.toModuleAut (R ⧸ I) I.Cotangent` an `R ⧸ I`-linear
action of the inertia group (a replacement for `cotangentInertiaAction`). -/
instance : SMulCommClass (I.inertia (MulAction.stabilizer M I)) (R ⧸ I) I.Cotangent where
  smul_comm τ c v := by
    rw [MulAction.subgroup_smul_def, stabilizer_smul_smul, inertia_smul_residue,
      ← MulAction.subgroup_smul_def]
end Ideal
end Action

end

-- From `SKW.Prereqs.FractionalIdeal`.
section

namespace FractionalIdeal

section General
variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]
  {G : Type*} [Group G] [MulSemiringAction G R] [MulSemiringAction G P] [SMulDistribClass G R P]
variable (hS : ∀ (g : G) {s : R}, s ∈ S → g • s ∈ S)
include hS
end General

section FractionRing
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
end FractionRing
end FractionalIdeal

theorem FractionalIdeal.num_ne_bot_of_ne_zero {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*}
    [CommRing P] [Algebra R P] [IsDomain R] [Module.IsTorsionFree R P] (hS : 0 ∉ S)
    {I : FractionalIdeal S P} (hI : I ≠ 0) :
    I.num ≠ ⊥ :=
  (zero_of_num_eq_bot hS).mt hI

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
  rw [count_coeIdeal K v hJ, Ideal.count_associates_factors_eq hJ v.isPrime v.ne_bot,
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

/-- Two nonzero fractional ideals are equal if and only if they have the same valuation at every
height one prime. -/
theorem FractionalIdeal.eq_iff_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I = J ↔ ∀ v : HeightOneSpectrum R, count K v I = count K v J := by
  refine ⟨fun h _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]
end count

section CountExtended
open Ideal IsDedekindDomain nonZeroDivisors
variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Algebra.IsIntegral R S] (K L : Type*) [Field K] [Field L] [Algebra R K]
  [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]

/-- The `w`-adic valuation of the extension of a fractional ideal `I` is the ramification index of
`w` times the valuation of `I` at the prime below `w`. -/
theorem FractionalIdeal.count_extendedHom [Module.IsTorsionFree R S] (w : HeightOneSpectrum S)
    (I : FractionalIdeal R⁰ K) :
    count L w (extendedHom L S I) = w.asIdeal.ramificationIdx R * count K (w.under R) I := by
  by_cases hI : I = 0
  · simp [hI, count_zero]
  have h' : Ideal.map (algebraMap R S) (span {↑I.den}) ≠ 0 := by simp [map_ne_bot_of_ne_bot]
  rw [FractionalIdeal.count_eq_multiplicity_num_sub _ _ hI, HeightOneSpectrum.under_asIdeal,
    mul_sub, ← Nat.cast_mul, ← Nat.cast_mul, ramificationIdx_mul_multiplicity_under_eq w.ne_bot,
    ramificationIdx_mul_multiplicity_under_eq w.ne_bot,
    ← FractionalIdeal.count_coe_mul_inv_eq_multiplicity_sub L _ _ h']
  · congr
    rw [eq_mul_inv_iff_mul_eq₀ (by simpa using h'), ← extendedHom_coeIdeal_eq_map _ S (K := K),
      ← map_mul, mul_comm, coeIdeal_span_singleton, den_mul_self_eq_num', extendedHom'_apply,
      extended_coeIdeal_eq_map]
  · apply map_ne_bot_of_ne_bot
    exact FractionalIdeal.num_ne_bot_of_ne_zero zero_notMem_nonZeroDivisors hI
end CountExtended

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
  rw [← coeToSubmodule_inj, coeToSubmodule_extended_eq_span, ringEquivOfRingEquiv_apply,
    coeToSubmodule_mk, ← Submodule.span_eq (Submodule.map _ _), Submodule.map_coe]
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
  · simp

theorem FractionalIdeal.smul_eq_ringEquivOfRingEquiv [IsDedekindDomain R] {G : Type*} [Group G]
    [MulSemiringAction G R] (g : G) (I : FractionalIdeal R⁰ K) :
    g • I = ringEquivOfRingEquiv K K (MulSemiringAction.toRingEquiv G R g) I := by
  rw [FractionalIdeal.smul_def, ringEquivOfRingEquiv_eq_extended]
  rfl

theorem FractionalIdeal.count_smul [IsDedekindDomain R] {G : Type*} [Group G]
    [MulSemiringAction G R] (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) (σ : G) :
    count K (σ • v) (σ • I) = count K v I := by
  rw [smul_eq_ringEquivOfRingEquiv, smul_eq_equivOfRingEquiv, count_ringEquivOfRingEquiv]
end FractionalIdealCount

end

-- From `SKW.Prereqs.IntermediateField`.
section

/-- The fixing subgroup of an intermediate field `F` is a Galois group of `L / F`. This bridges
`IntermediateField.fixingSubgroup` to `IsGaloisGroup.intermediateField`, which is stated on the raw
`fixingSubgroup Gal(L/K) (↑F)`; instance search does not unfold the
  `IntermediateField.fixingSubgroup`
wrapper on its own, so without this the instance is not found for the `IntermediateField` form. -/
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) : IsGaloisGroup F.fixingSubgroup F L :=
  inferInstanceAs (IsGaloisGroup (fixingSubgroup Gal(L/K) (F : Set L)) F L)

open scoped NumberField in
/-- Ring-of-integers form of the previous instance. The generic `IsGaloisGroup G (𝓞 K) (𝓞 L)`
instance does not fire for `G = F.fixingSubgroup` on its own, so we bridge it explicitly (its body,
`IsGaloisGroup.of_isFractionRing`, uses the field instance above). Keying on `F.fixingSubgroup` (as
opposed to an arbitrary `G`) is essential: it pins the intermediate field `F`, which otherwise would
only be recoverable from `𝓞 ↑F` and hence left undetermined by instance search. -/
instance {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (F : IntermediateField K L) :
    IsGaloisGroup F.fixingSubgroup (𝓞 F) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing _ (𝓞 F) (𝓞 L) F L

open IntermediateField in
/-- In a finite Galois extension, two intermediate fields are equal iff they have the same fixing
subgroup. -/
theorem IsGalois.fixingSubgroup_inj {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {F₁ F₂ : IntermediateField K L} :
    F₁.fixingSubgroup = F₂.fixingSubgroup ↔ F₁ = F₂ :=
  ⟨fun h ↦ by rw [← fixedField_fixingSubgroup F₁, h, fixedField_fixingSubgroup], congr_arg _⟩

open IntermediateField in
/-- In a finite extension, two subgroups of the automorphism group are equal iff they have the same
fixed field. -/
theorem IsGalois.fixedField_inj {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {H₁ H₂ : Subgroup Gal(L/K)} :
    fixedField H₁ = fixedField H₂ ↔ H₁ = H₂ :=
  ⟨fun h ↦ by rw [← fixingSubgroup_fixedField H₁, h, fixingSubgroup_fixedField], congr_arg _⟩

open IntermediateField in
/-- `lift` preserves the degree over the base field: `[lift E : K] = [E : K]`. -/
theorem IntermediateField.finrank_lift {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} (E : IntermediateField K F) :
    Module.finrank K (lift E) = Module.finrank K E :=
  (liftAlgEquiv E).toLinearEquiv.finrank_eq.symm

open IntermediateField in
/-- `restrict` preserves the degree over the base field: `[restrict h : K] = [F : K]`. -/
theorem IntermediateField.finrank_restrict {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F E : IntermediateField K L} (h : F ≤ E) :
    Module.finrank K (restrict h) = Module.finrank K F :=
  (restrictAlgEquiv h).toLinearEquiv.finrank_eq.symm

open IntermediateField in
/-- `restrict` preserves finite-dimensionality over the base field. -/
instance IntermediateField.finiteDimensional_restrict {K L : Type*} [Field K] [Field L]
    [Algebra K L] {F E : IntermediateField K L} {h : F ≤ E} [FiniteDimensional K F] :
    FiniteDimensional K (restrict h) :=
  Module.Finite.equiv (restrictAlgEquiv h).toLinearEquiv

/-- Fixed-field is antitone (the Galois correspondence), so it sends `⊓` of subgroups to `⊔` of
fixed fields: `fixedField (A ⊓ B) = fixedField A ⊔ fixedField B`. -/
theorem FixedPoints.intermediateField_inf (G K L : Type*) [Group G] [Field K] [Field L]
    [Algebra K L] [MulSemiringAction G L] [Finite G] [IsGaloisGroup G K L] (A B : Subgroup G) :
    (FixedPoints.intermediateField ↑(A ⊓ B) : IntermediateField K L) =
      FixedPoints.intermediateField A ⊔ FixedPoints.intermediateField B := by
  rw [← IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual G K L (H := A ⊓ B),
    ← IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual G K L (H := A),
    ← IsGaloisGroup.intermediateFieldEquivSubgroup_symm_apply_toDual G K L (H := B),
    toDual_inf, OrderIso.map_sup]

/-- **Inertia field from a complement.** For a Galois group `G` of `L/K` (`IsGaloisGroup G K L`), if
a normal subgroup `I` is complemented by the fixing subgroup of an intermediate field `F`
(`IsComplement' I (fixingSubgroup G (F : Set L))`), then the fixed field of `I` together with `F`
generates `L`, and the complement is `G ⧸ I`. Used both in the odd-prime ramification reduction and
in the `p = 2` (Lemmermeyer) case, each taking a fixed field of a subgroup this way. -/
theorem IsGaloisGroup.fixedPoints_sup_eq_top_of_isComplement (G K L : Type*) [Group G] [Field K]
    [Field L] [Algebra K L] [MulSemiringAction G L] [Finite G] [IsGaloisGroup G K L]
    {I : Subgroup G} [I.Normal] {F : IntermediateField K L}
    (h : Subgroup.IsComplement' I (fixingSubgroup G (F : Set L))) :
    FixedPoints.intermediateField I ⊔ F = ⊤ ∧
      Nonempty (G ⧸ I ≃* (fixingSubgroup G (F : Set L))) := by
  refine ⟨?_, ⟨h.symm.QuotientMulEquiv⟩⟩
  rw [← fixedPoints_fixingSubgroup G K L F, ← FixedPoints.intermediateField_inf,
    disjoint_iff.mp h.disjoint, fixedPoints_bot]

section restrictScalars
variable (K F E L : Type*) [Field K] [Field F] [Field E] [Field L]
  [Algebra K F] [Algebra K E] [Algebra K L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower K F E] [IsScalarTower K F L] [IsScalarTower K E L] [IsScalarTower F E L]
  [FiniteDimensional K L] [FiniteDimensional K E] [FiniteDimensional F L] [FiniteDimensional F E]
  [IsGalois K L] [IsGalois K E] [IsGalois F L] [IsGalois F E]
end restrictScalars

section restrictHom_eq
variable (G G' A B C A' B' C' : Type*) [Group G] [Group G'] [Finite G] [Finite G']
  [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower A B C] [FaithfulSMul B C]
  [MulSemiringAction G C] [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B]
  [CommRing A'] [CommRing B'] [CommRing C'] [IsDomain C'] [Algebra A' B'] [Algebra A' C']
  [Algebra B' C'] [IsScalarTower A' B' C'] [FaithfulSMul B' C']
  [MulSemiringAction G C'] [IsGaloisGroup G A' C'] [MulSemiringAction G' B']
  [IsGaloisGroup G' A' B']
  [Algebra B B'] [Algebra C C'] [Algebra B C'] [IsScalarTower B B' C'] [IsScalarTower B C C']
  [FaithfulSMul B B'] [SMulDistribClass G C C'] [SMulDistribClass G' B B']
end restrictHom_eq
universe u

open IntermediateField in
/-- Every finite-dimensional abelian Galois extension `K/F` is the compositum of cyclic
subextensions of prime power degree. (The character codomain is `AlgebraicClosure ℚ`, which has
enough roots of unity for the finite group `Gal(K/F)` regardless of the characteristic of `F`.) -/
lemma IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top
    (F : Type*) (K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsAbelianGalois F K] :
    ∃ (ι : Type u) (_ : Fintype ι) (C : ι → IntermediateField F K),
      (∀ i, IsGalois F (C i) ∧ IsCyclic Gal((C i)/F) ∧ IsPrimePow (Module.finrank F (C i))) ∧
        ⨆ i, C i = ⊤ := by
  classical
  let : CommGroup (K ≃ₐ[F] K) := IsMulCommutative.instCommGroup
  refine ⟨{χ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ // IsPrimePow (orderOf χ)}, Fintype.ofFinite _,
    fun χ ↦ IntermediateField.fixedField χ.1.ker, fun ⟨χ, hχ⟩ ↦ ?_, ?_⟩
  · refine ⟨IsGalois.of_fixedField_normal_subgroup χ.ker, ?_, ?_⟩
    · exact isCyclic_of_injective (IsGalois.normalAutEquivQuotient χ.ker).symm.toMonoidHom
        (MulEquiv.injective _)
    · have : IsGalois F (fixedField χ.ker) := IsGalois.of_fixedField_normal_subgroup χ.ker
      rw [← IsGalois.card_aut_eq_finrank]
      erw [Nat.card_congr (IsGalois.normalAutEquivQuotient χ.ker).symm.toEquiv]
      rwa [MonoidHom.card_quotient_ker_eq_orderOf χ]
  · simp only [← IsGalois.intermediateFieldEquivSubgroup.apply_eq_iff_eq, OrderIso.map_iSup,
      IsGalois.intermediateFieldEquivSubgroup_apply, fixingSubgroup_fixedField, OrderIso.map_top,
      ← toDual_iInf, OrderDual.toDual_eq_top]
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
    by_contra! h
    have h_eq_one {ψ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ} : ψ g = 1 := by
      have : ψ ∈ Subgroup.closure
          {χ : Gal(K/F) →* (AlgebraicClosure ℚ)ˣ| IsPrimePow (orderOf χ)} := by
        rw [CommGroup.closure_isPrimePow_orderOf_eq_top isMulTorsion_of_finite]
        exact Subgroup.mem_top ψ
      induction this using Subgroup.closure_induction with
      | mem η hη => exact Subgroup.mem_iInf.mp hg ⟨η, hη⟩
      | one => simp
      | mul η₁ η₂ _ _ h₁ h₂ => rw [MonoidHom.mul_apply, h₁, h₂, one_mul]
      | inv η _ hη => rw [MonoidHom.inv_apply, hη, inv_eq_one]
    obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(K/F)
      (AlgebraicClosure ℚ) h
    exact hψ h_eq_one

open IntermediateField Module in
/-- If `B / F` is a finite Galois extension and the compositum `A ⊔ B` is all of `E`, then the
relative degree `[E : A]` divides `[B : F]`. This is the ⊤-case: here `E` is genuinely an
`A`-algebra, so the divisibility can be stated directly (unlike the general compositum form
`finrank_sup_dvd_mul_of_isGalois`). It follows from the injection `Gal(E/A) ↪ Gal(B/F)` induced by
restriction and Lagrange's theorem. -/
theorem IntermediateField.finrank_dvd_finrank_of_isGalois_of_sup_eq_top {F E : Type*} [Field F]
    [Field E] [Algebra F E] (A B : IntermediateField F E)
    [FiniteDimensional A E] [FiniteDimensional F B] [IsGalois F B] (h : B ⊔ A = ⊤) :
    finrank A E ∣ finrank F B := by
  have : IsGalois A E := IsGalois.sup_right B A h
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_dvd_of_injective _ <| restrictRestrictAlgEquivMapHom_injective B A h

open Module in
/-- If `B / F` is a finite Galois extension, then for any finite `A`, the degree of the compositum
`A ⊔ B` over `F` divides `[A : F] * [B : F]`. (Equivalently, `[A ⊔ B : A] ∣ [B : F]`, which fails
without the Galois hypothesis on `B`.)

Remark: we cannot state this as `finrank A ↑(A ⊔ B) ∣ finrank F B` since `↑(A ⊔ B)` is not, by
default, an `A`-algebra; hence the product form `[A ⊔ B : F] ∣ [A : F] * [B : F]`. The ⊤-case
`finrank_dvd_finrank_of_isGalois_of_sup_eq_top` does not have this obstruction. -/
theorem IntermediateField.finrank_sup_dvd_mul_of_isGalois {F E : Type*} [Field F] [Field E]
    [Algebra F E] (A B : IntermediateField F E) [FiniteDimensional F A] [IsGalois F B]
    [FiniteDimensional F B] :
    finrank F ↑(A ⊔ B) ∣ finrank F A * finrank F B := by
  let A' : IntermediateField F ↑(A ⊔ B) := A.restrict le_sup_left
  let B' : IntermediateField F ↑(A ⊔ B) := B.restrict le_sup_right
  have : IsGalois F B' := IsGalois.of_algEquiv (restrictAlgEquiv le_sup_right)
  -- TODO: workaround for a slow `IsTorsionFree` instance search, see the plan; drop once fixed.
  have : Module.Free A' ↑(A ⊔ B) := Module.Free.of_divisionRing _ _
  have : B' ⊔ A' = ⊤ :=
    lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_top, sup_comm])
  have := mul_dvd_mul_left (finrank F A') <| finrank_dvd_finrank_of_isGalois_of_sup_eq_top A' B'
    this
  rwa [Module.finrank_mul_finrank, finrank_restrict, finrank_restrict] at this

theorem IntermediateField.lift_iSup (F E : Type*) [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) {ι : Type*} (S : Finset ι) (L : ι → IntermediateField F K) :
    lift (⨆ i ∈ S, L i) = ⨆ i ∈ S, lift (L i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i s _ hi => rw [Finset.iSup_insert, Finset.iSup_insert, lift_sup, hi]

namespace IntermediateField
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {K : IntermediateField F E}
end IntermediateField

namespace IntermediateField
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- If `L / K` has prime degree, then any intermediate field between `K` and `L` is `K` or `L`. -/
theorem eq_or_eq_of_relfinrank_prime {K L M : IntermediateField F E} (hKM : K ≤ M) (hML : M ≤ L)
    (hp : (relfinrank K L).Prime) : M = K ∨ M = L := by
  rw [← relfinrank_mul_relfinrank hKM hML, Nat.prime_mul_iff] at hp
  obtain ⟨-, h⟩ | ⟨-, h⟩ := hp
  · exact .inr <| le_antisymm hML (relfinrank_eq_one_iff.mp h)
  · exact .inl <| le_antisymm (relfinrank_eq_one_iff.mp h) hKM
end IntermediateField

end

-- From `SKW.Prereqs.KummerExtension`.
section
open IntermediateField Polynomial

section
open Polynomial IntermediateField

/-- If `ζ` is a primitive `n`-th root of unity and `x ^ n = α ^ n`, then `x = ζ ^ j * α`
for some `j < n`. Generalizes the implicit content of `IsPrimitiveRoot.nthRoots_eq`. -/
lemma IsPrimitiveRoot.eq_pow_mul_of_pow_eq {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} [NeZero n] {ζ α x : R}
    (hζ : IsPrimitiveRoot ζ n) (h : x ^ n = α ^ n) :
    ∃ j : ℕ, j < n ∧ x = ζ ^ j * α := by
  have hx : x ∈ nthRoots n (α ^ n) := (mem_nthRoots (NeZero.pos n)).mpr h
  simp only [hζ.nthRoots_eq rfl, Multiset.mem_map, Multiset.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, hj, rfl⟩

/-- Version of `Algebra.adjoin_root_eq_top_of_isSplittingField` without the irreducibility of
`X ^ n - C a`. -/
lemma Algebra.adjoin_root_eq_top_of_isSplittingField' {K : Type*} [Field K] {n : ℕ}
    (hζ : (primitiveRoots n K).Nonempty) {a : K} {L : Type*} [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ n - C a)] {α : L} (hα : α ^ n = algebraMap K L a) :
    Algebra.adjoin K {α} = ⊤ := by
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero n := ⟨fun h ↦ by simp [h] at hζ⟩
  replace hζ := (isPrimitiveRoot_of_mem_primitiveRoots hζ).map_of_injective
    (algebraMap K L).injective
  rw [← top_le_iff, ← IsSplittingField.adjoin_rootSet L (X ^ n - C a), Algebra.adjoin_le_iff]
  intro x hx
  rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero (NeZero.pos n) a), aeval_sub, aeval_X_pow, aeval_C,
    sub_eq_zero, ← hα] at hx
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_mul_of_pow_eq hx
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) _)
    (Algebra.self_mem_adjoin_singleton K α)

/-- Version of `IntermediateField.adjoin_root_eq_top_of_isSplittingField` without the
irreducibility of `X ^ n - C a`. -/
lemma IntermediateField.adjoin_root_eq_top_of_isSplittingField' {K : Type*} [Field K] {n : ℕ}
    (hζ : (primitiveRoots n K).Nonempty) {a : K} {L : Type*} [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ n - C a)] {α : L} (hα : α ^ n = algebraMap K L a) : K⟮α⟯ = ⊤ :=
  (eq_adjoin_of_eq_algebra_adjoin _ _ _
    (Algebra.adjoin_root_eq_top_of_isSplittingField' hζ hα).symm).symm

/-- If `K` contains a primitive `n`-th root of unity and the splitting field `L` of `X ^ n - C a`
has degree `n` over `K`, then `X ^ n - C a` is irreducible. -/
lemma irreducible_X_pow_sub_C_of_isSplittingField {K : Type*} [Field K] {n : ℕ}
    (hζ : (primitiveRoots n K).Nonempty) {a : K} {L : Type*} [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ n - C a)] (hn : Module.finrank K L = n) :
    Irreducible (X ^ n - C a) := by
  have : NeZero n := ⟨fun h ↦ by simp [h] at hζ⟩
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L (X ^ n - C a)
  obtain ⟨α, hα⟩ : ∃ α : L, α ^ n = algebraMap K L a := ⟨_, rootOfSplitsXPowSubC_pow a L⟩
  have htop := IntermediateField.adjoin_root_eq_top_of_isSplittingField' hζ hα
  rw [← hn] at hα ⊢
  exact irreducible_X_pow_sub_C_of_root_adjoin_eq_top hα htop

/-- Kummer group characterization: let `K` be a field with a primitive `n`-th root of unity `ζ`,
`a ∈ Kˣ` with `X ^ n - a` irreducible, `α` a root of `X ^ n - a` in `L = K(α)`, and
`σ ∈ Gal(L/K)` the automorphism defined by `σ(α) = ζ * α`.
If `β ∈ L` satisfies `β ^ n ∈ Kˣ`, then `β = λ * α ^ j` for some `λ ∈ K` and `j < n`. -/
theorem exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap {K : Type*} [Field K] {n : ℕ} [NeZero n]
    (hK : (primitiveRoots n K).Nonempty) {L : Type*} [Field L] [Algebra K L] {a : K}
    (hIrr : Irreducible (X ^ n - C a)) [IsSplittingField K L (X ^ n - C a)] {α : L}
    (hα : α ^ n = algebraMap K L a) {β : L} {b : K} (hβ : β ^ n = algebraMap K L b) :
    ∃ (c : K) (j : ℕ), j < n ∧ β = algebraMap K L c * α ^ j := by
  classical
  have hmp : minpoly K α = X ^ n - C a :=
    (minpoly.eq_of_irreducible_of_monic hIrr (by simp [hα])
      (monic_X_pow_sub_C a (NeZero.ne n))).symm
  have hint : IsIntegral K α := ⟨X ^ n - C a, monic_X_pow_sub_C a (NeZero.ne n),
    hmp ▸ minpoly.aeval K α⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_root_eq_top_of_isSplittingField hK hIrr hα
  obtain ⟨ζ, hζ⟩ := hK
  replace hζ : IsPrimitiveRoot ζ n := isPrimitiveRoot_of_mem_primitiveRoots hζ
  let σ := (autEquivZmod hIrr L hζ).symm (Multiplicative.ofAdd 1)
  have hσ : σ α = algebraMap K L ζ * α := by
    have := autEquivZmod_symm_apply_natCast hIrr L hα hζ 1
    rwa [pow_one, Algebra.smul_def, Nat.cast_one] at this
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n := hζ.map_of_injective (algebraMap K L).injective
  have hσβn : (σ β) ^ n = β ^ n := by rw [← map_pow, hβ, AlgEquiv.commutes]
  obtain ⟨j, hj, hσβ⟩ := hζL.eq_pow_mul_of_pow_eq hσβn
  let B := PowerBasis.ofAdjoinSimpleEqTop hint hgen
  have hsB {i} : σ (B.basis i) = algebraMap K L ζ ^ i.val * (B.basis i) := by
    simp [PowerBasis.coe_basis, B, hσ, mul_pow]
  have hdB : B.dim = n := by rw [PowerBasis.ofAdjoinSimpleEqTop_dim, hmp, natDegree_X_pow_sub_C]
  let j₀ : Fin B.dim := ⟨j, by rwa [hdB]⟩
  refine ⟨B.basis.equivFun β j₀, j, hj, ?_⟩
  have h₀ := B.basis.sum_equivFun β
  nth_rewrite 1 [← h₀]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have {i} (hi : i ∈ Finset.univ.erase j₀) : B.basis.equivFun β i = 0 := by
    have h₁ := (congr_arg σ h₀).trans hσβ
    nth_rewrite 2 [← h₀] at h₁
    simp_rw [map_sum, map_smul, hsB] at h₁
    rw [Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
    simp_rw [Algebra.smul_def, ← mul_assoc, ← map_pow, ← map_mul, ← sub_mul, ← map_sub,
      ← Algebra.smul_def, mul_comm, ← sub_mul] at h₁
    have := linearIndependent_iff'.mp B.basis.linearIndependent _ _ h₁ i (Finset.mem_univ i)
    rwa [mul_eq_zero_iff_left] at this
    contrapose hi
    simpa [j₀, Fin.ext_iff] using hζ.pow_inj (Fin.val_lt_of_le i hdB.le) hj (sub_eq_zero.mp hi)
  simp +contextual [j₀, this, Algebra.smul_def, B]
variable {F : Type*} [Field F] {n : ℕ} [NeZero n] {K : Type*} [Field K] [Algebra K F]
  [IsGalois K F] {μ : F} {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
open Module
end

/-- Version of `exists_root_adjoin_eq_top_of_isCyclic` with a nonzero root `α`. -/
theorem exists_root_adjoin_eq_top_of_isCyclic' (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (hK : (primitiveRoots (Module.finrank K L) K).Nonempty) :
    ∃ α : L, α ≠ 0 ∧ α ^ Module.finrank K L ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤ := by
  obtain ⟨α, hα, hα'⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  obtain rfl | h := eq_or_ne α 0
  · rw [adjoin_zero] at hα'
    exact ⟨1, one_ne_zero, ⟨1, by simp⟩, by rwa [adjoin_one]⟩
  · exact ⟨α, h, hα, hα'⟩

end

-- From `SKW.Prereqs.TameRamification`.
section

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
filtration: from `τ • x ≡ x mod Q ^ 2` on `Q`,
  one gets `τ • x ≡ x mod Q ^ (n + 2)` on `Q ^ (n+1)`. -/
theorem sub_mem_pow_of_sub_mem (Q : Ideal S) (τ : Q.inertia (MulAction.stabilizer G Q))
    (h : ∀ x ∈ Q, τ • x - x ∈ Q ^ 2) (n : ℕ) {x : S} (hx : x ∈ Q ^ n) :
    τ • x - x ∈ Q ^ (n + 1) := by
  induction n generalizing x with
  | zero =>
    simp_all only [pow_zero, one_eq_top, Submodule.mem_top, zero_add, pow_one]
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
      have h₂ : ∑ k ∈ Finset.range (orderOf τ),
        Ideal.Quotient.mk (Q ^ (n + 1)) (τ ^ k • δ) = 0 := by
        simp only [δ_def, smul_sub, smul_smul, ← pow_succ]
        rw [← map_sum, Finset.sum_range_sub (fun k ↦ τ ^ k • x), pow_orderOf_eq_one τ, pow_zero,
          sub_self, map_zero]
      simp_rw [h₁, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h₂
      rwa [IsUnit.mul_right_eq_zero, Quotient.eq_zero_iff_mem] at h₂
      exact Quotient.isUnit_mk_pow_of_notMem _ hord

/-- The localization of a Dedekind domain at a nonzero maximal ideal is a discrete valuation ring.
A local instance so that `Ideal.finrank_cotangent_eq_one` applies to the cotangent line
  `Q ⧸ Q ^ 2`. -/
private instance [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q] :
    IsDiscreteValuationRing (Localization.AtPrime Q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S (NeZero.ne Q) _

/-- In dimension one, the cotangent action of an inertia element is the homothety by its tame
character: `cotangentInertiaAction G Q τ = θ(τ) • id`. -/
theorem cotangentInertiaAction_apply_eq_smul [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal]
    [NeZero Q] (τ : Q.inertia (MulAction.stabilizer G Q)) (v : Q.Cotangent) :
    τ • v = (tameCharacter G Q τ).val • v := by
  let := Ideal.Quotient.field Q
  rw [tameCharacter_apply, LinearEquiv.coe_det]
  exact LinearMap.apply_eq_det_smul_of_finrank_eq_one Q.finrank_cotangent_eq_one
    (DistribMulAction.toLinearEquiv (S ⧸ Q) Q.Cotangent τ) v

/-- (Rigidity, L1) If `θ(τ) = 1` then `τ` fixes the cotangent line `Q ⧸ Q ^ 2`: for `x ∈ Q`,
`τ • x ≡ x mod Q ^ 2`. Uses that `Q ⧸ Q ^ 2` is one-dimensional over the field `S ⧸ Q`, so
`det = 1` forces the action to be the identity. -/
theorem sub_mem_sq_of_tameCharacter_eq_one [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero
  Q]
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
theorem eq_one_of_forall_sub_mem_pow [IsDedekindDomain S] [FaithfulSMul G S] (Q : Ideal S)
    [hQ : Q.IsMaximal] (τ : Q.inertia (MulAction.stabilizer G Q))
    (h : ∀ (n : ℕ) (x : S), τ • x - x ∈ Q ^ n) : τ = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := S) fun x ↦ ?_
  simpa [iInf_pow_eq_bot_of_isDomain _ hQ.ne_top, sub_eq_zero] using mem_iInf.mpr fun i ↦ h i x

/-- **Rigidity** (filtration-free): an inertia element of order prime to the residue
characteristic on which the tame character vanishes is trivial. -/
theorem eq_one_of_tameCharacter_eq_one [IsDedekindDomain S] [FaithfulSMul G S] (Q : Ideal S)
    [Q.IsMaximal] [NeZero Q] (τ : Q.inertia (MulAction.stabilizer G Q)) (hord : ↑(orderOf τ) ∉ Q)
    (h : tameCharacter G Q τ = 1) : τ = 1 := by
  apply eq_one_of_forall_sub_mem_pow
  apply sub_mem_pow_of_coprime
  · apply sub_mem_pow_of_sub_mem
    exact fun x a ↦ sub_mem_sq_of_tameCharacter_eq_one Q τ h a
  · exact hord

variable (G) in
theorem tameCharacter_injective [IsDedekindDomain S] [FaithfulSMul G S] (Q : Ideal S) [Q.IsMaximal]
    [NeZero Q] (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    Function.Injective (tameCharacter G Q) := by
  refine (injective_iff_map_eq_one _).mpr fun τ hτ ↦ eq_one_of_tameCharacter_eq_one _ _ ?_ hτ
  contrapose htame
  obtain ⟨q, hq⟩ := Nat.cast_dvd_cast (α := S) <| orderOf_dvd_natCard τ
  exact hq ▸ Ideal.mul_mem_right _ _ htame

attribute [local instance] Ideal.Quotient.field in
/-- **Frobenius equivariance**: conjugating an inertia element by an arithmetic Frobenius
raises the tame character to the `N 𝔭`-th power. (Conjugation lands back in inertia by
normality, via `MulAut.conjNormal`.) -/
theorem tameCharacter_conj [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
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
theorem isCyclic_inertia [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q] [Finite (S ⧸
  Q)] [FaithfulSMul G S]
    (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    IsCyclic (Q.inertia (MulAction.stabilizer G Q)) :=
  isCyclic_of_injective _ (tameCharacter_injective G Q htame)

/-- **Abelian tame ramification**: for an abelian action, the order of the inertia group
(the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    [FaithfulSMul G S] [Finite G] [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)] [IsMulCommutative G]
    (htame : ↑(Nat.card (Q.inertia (MulAction.stabilizer G Q))) ∉ Q) :
    Nat.card (Q.inertia (MulAction.stabilizer G Q)) ∣ Nat.card (R ⧸ Q.under R) - 1 := by
  obtain ⟨τ, hτ⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp <| isCyclic_inertia Q htame
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant R G Q
  rw [← hτ, ← orderOf_injective _ (tameCharacter_injective G Q htame), ← Int.natCast_dvd_natCast,
    orderOf_dvd_iff_zpow_eq_one, Nat.cast_sub hσ.card_pos, Nat.cast_one, zpow_sub_one,
    zpow_natCast, ← tameCharacter_conj Q ⟨σ, hσ.mem_stabilizer⟩ hσ.of_coe τ,
    MulAut.conjNormal_apply_of_isMulCommutative, mul_inv_cancel]

variable (G) in
/-- Inertia computed inside the full group `G` agrees with inertia computed inside the decomposition
group `MulAction.stabilizer G Q`: every inertia element fixes `Q` (`inertia_le_stabilizer`), so the
inclusion of the decomposition group restricts to an isomorphism of inertia groups. -/
def inertiaStabilizerEquiv (Q : Ideal S) :
    Q.inertia (MulAction.stabilizer G Q) ≃* Q.inertia G :=
  Subgroup.subgroupOfEquivOfLe Q.inertia_le_stabilizer

/-- **Rigidity, full-group form** of `isCyclic_inertia`: tame inertia inside the full group `G`
(not merely inside the decomposition group) is cyclic. -/
theorem isCyclic_inertia' [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    [Finite (S ⧸ Q)] [FaithfulSMul G S] (htame : ↑(Nat.card (Q.inertia G)) ∉ Q) :
      IsCyclic (Q.inertia G) :=
  (inertiaStabilizerEquiv G Q).isCyclic.mp <|
    isCyclic_inertia Q (by rwa [Nat.card_congr (inertiaStabilizerEquiv G Q).toEquiv])

/-- The tameness hypothesis `↑(Nat.card (Q.inertia G)) ∉ Q` used by `isCyclic_inertia'` is exactly
the classical tameness condition: the residue characteristic (`absNorm` of the prime `Q ∩ ℤ`) does
not divide the ramification index `e(Q)`. -/
theorem card_inertia_notMem_iff [IsDomain S] (Q : Ideal S) [Q.IsPrime] [Module.Finite ℤ S]
    [Module.Flat ℤ S] [IsGaloisGroup G ℤ S] [Finite G] :
    ↑(Nat.card (Q.inertia G)) ∉ Q ↔ ¬ (under ℤ Q).absNorm ∣ ramificationIdx Q ℤ := by
  rw [← Int.cast_natCast, Int.cast_mem_ideal_iff, Int.natCast_dvd_natCast,
    card_inertia_eq_ramificationIdxIn (under ℤ Q), ramificationIdxIn_eq_ramificationIdx _ Q G]

/-- **Abelian tame ramification,
  full-group form** of `card_inertia_dvd_card_sub_one`: for an abelian
action the order of the full-group inertia (the ramification index) divides `N𝔭 - 1`. -/
theorem card_inertia_dvd_card_sub_one' [IsDedekindDomain S] (Q : Ideal S) [Q.IsMaximal] [NeZero Q]
    [FaithfulSMul G S] [Finite G] [Algebra.IsInvariant R S G] [Finite (S ⧸ Q)] [IsMulCommutative G]
    (htame : ↑(Nat.card (Q.inertia G)) ∉ Q) :
    Nat.card (Q.inertia G) ∣ Nat.card (R ⧸ Q.under R) - 1 := by
  rw [← Nat.card_congr (inertiaStabilizerEquiv G Q).toEquiv]
  exact card_inertia_dvd_card_sub_one Q
    (by rwa [Nat.card_congr (inertiaStabilizerEquiv G Q).toEquiv])
end Ideal

end

-- From `SKW.Prereqs.Unramified`.
section

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

-- From `SKW.Prereqs.CyclotomicField`.
section

theorem IsCyclotomicExtension.primitiveRoots_nonempty (n : ℕ) [NeZero n] (A B : Type*) [CommRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [hC : IsCyclotomicExtension {n} A B] :
    (primitiveRoots n B).Nonempty :=
  ⟨hC.zeta, (mem_primitiveRoots (NeZero.pos n)).mpr hC.zeta_spec⟩
open IntermediateField
open IsCyclotomicExtension.Rat NumberField

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat in
/-- An automorphism `σ` sends `ζ` to `ζ ^ k` exactly when `galEquivZMod` sends `σ` to `k`. -/
theorem IsCyclotomicExtension.Rat.apply_eq_pow_iff_galEquivZMod_eq {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] {σ : Gal(K/ℚ)}
    {k : ZMod n} {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    σ ζ = ζ ^ k.val ↔ galEquivZMod n K σ = k := by
  rw [galEquivZMod_apply_of_pow_eq n K σ hζ.pow_eq_one, ← (hζ.isUnit (NeZero.ne n)).unit_spec ,
    ←  Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.ext_iff, pow_eq_pow_iff_modEq,
    ← (hζ.isUnit_unit (NeZero.ne n)).eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

open IsCyclotomicExtension IsCyclotomicExtension.Rat in
/-- In a cyclotomic field, complex conjugation corresponds to `-1` under `galEquivZMod`. -/
theorem IsCyclotomicExtension.Rat.galEquivZMod_ratComplexConj (n : ℕ) [NeZero n] (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsCMField K] :
    galEquivZMod n K (IsCMField.ratComplexConj K) = -1 := by
  rw [Units.ext_iff, Units.val_neg, Units.val_one,
    show (-1 : ZMod n) = ((n - 1  : ℕ): ZMod n) by simp [Nat.cast_sub NeZero.one_le],
    ← apply_eq_pow_iff_galEquivZMod_eq (zeta_spec n ℚ K), IsCMField.ratComplexConj_apply,
    IsCMField.complexConj_eq_inv_of_isPrimitiveRoot (zeta_spec n ℚ K), ZMod.val_natCast,
    Nat.self_sub_mod, ← zpow_natCast, Nat.cast_sub NeZero.one_le, Nat.cast_one, zpow_sub_one₀
    ((zeta_spec n ℚ K).ne_zero (NeZero.ne n)), zpow_natCast, (zeta_spec n ℚ K).pow_eq_one, one_mul]

namespace IsCyclotomicExtension.Rat
open Ideal NumberField
variable (p k : ℕ) [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [NumberField K]

-- TODO: in Mathlib, this should eventually replace `isPrime_span_zeta_sub_one`.
instance isMaximal_span_zeta_sub_one [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : IsMaximal (span {hζ.toInteger - 1}) :=
  (isPrime_span_zeta_sub_one p k hζ).isMaximal (span_zeta_sub_one_ne_bot p k hζ)
end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat
open NumberField IsCMField Units Ideal
variable (p k : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCMField K]

attribute [local instance] Ideal.Quotient.field in
/-- For an odd prime `p`, the units of `ℚ(ζ_{p^(k+1)})` are generated by the real units and the
roots of unity. -/
theorem indexRealUnits_eq_one [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] (hp₂ : p ≠ 2) :
    indexRealUnits K = 1 := by
  refine (indexRealUnits_eq_one_or_two K).resolve_right fun h ↦ ?_
  obtain ⟨u, hu⟩ := (indexRealUnits_eq_two_iff K).mp h
  set η := unitsMulComplexConjInv K u
  -- The generator `η` of the torsion has order `2 * p ^ (k + 1)`.
  have h₁ : orderOf η = p ^ (k + 1) * 2 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hu, ← torsionOrder, torsionOrder_eq (n := p ^ (k + 1)),
      ite_eq_right, mul_comm]
    rw [Nat.not_even_iff_odd, Nat.odd_pow_iff (NeZero.ne _)]
    exact hp.out.odd_of_ne_two hp₂
  -- Hence `η ^ p ^ (k + 1) = -1`.
  have h₂ : ((η ^ p ^ (k + 1) : torsion K) : (𝓞 K)ˣ) = (-1 : 𝓞 K):= by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    apply IsPrimitiveRoot.pow (by grind [hp.out.pos]) ?_ rfl
    rwa [IsPrimitiveRoot.iff_orderOf, orderOf_units, Subgroup.orderOf_coe]
  -- Complex conjugation is trivial modulo `ζ - 1`, so `η ≡ 1`.
  let hζ := zeta_spec (p ^ (k + 1)) ℚ K
  have h₃ : Ideal.Quotient.mk (span {hζ.toInteger - 1}) ((η : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [unitsMulComplexConjInv_apply, val_mul, map_mul, map_units_inv, coe_unitsComplexConj,
      ← RingHom.coe_coe (ringOfIntegersComplexConj K), quotientMk_span_zeta_sub_one_comp_apply,
      mul_inv_cancel₀]
    exact fun h ↦ IsMaximal.ne_top inferInstance <|
      eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp h) u.isUnit
  -- Then `-1 ≡ 1`, so `ζ - 1` divides `2`.
  apply hζ.toInteger_sub_one_not_dvd_two hp₂
  have := congr_arg (· ^ p ^ (k + 1)) h₃
  rw [one_pow] at this
  rw [← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← one_add_one_eq_two, map_add,
    ← eq_neg_iff_add_eq_zero, ← map_neg, map_one, ← this, ← h₂, SubmonoidClass.coe_pow,
    val_pow_eq_pow_val, map_pow]

theorem indexRealUnits_eq_one' [hK : IsCyclotomicExtension {p} ℚ K] (hp₂ : p ≠ 2) :
    indexRealUnits K = 1 := by
  rw [← pow_one p] at hK
  exact indexRealUnits_eq_one p 0 K hp₂
end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

section
variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]

/-- The Galois group of `ℚ(ζₙ)` is cyclic iff `(ℤ/nℤ)ˣ` is cyclic. -/
theorem isCyclic_iff_isCyclic_units : IsCyclic Gal(K/ℚ) ↔ IsCyclic (ZMod n)ˣ :=
  (galEquivZMod n K).isCyclic
end
variable (K : Type*) [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

/-- The Galois group of `ℚ(ζ_{p ^ k})` is cyclic for `p` an odd prime. -/
theorem isCyclic_of_prime_pow (k : ℕ) (hp' : p ≠ 2) [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclic Gal(K/ℚ) :=
  (isCyclic_iff_isCyclic_units (p ^ k) K).mpr (ZMod.isCyclic_units_of_prime_pow p hp.out hp' k)
end IsCyclotomicExtension.Rat

end
