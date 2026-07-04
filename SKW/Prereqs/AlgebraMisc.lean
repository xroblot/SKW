module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

public import SKW.PRed2Mathlib.AlgebraMisc

@[expose] public section

theorem Algebra.adjoin_singleton_add {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A)
    (y : R) : adjoin R {x + algebraMap R A y} = adjoin R {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact add_mem (self_mem_adjoin_singleton R x) (algebraMap_mem _ y)
  · apply adjoin_singleton_le
    convert Subalgebra.sub_mem _ (self_mem_adjoin_singleton R _) (algebraMap_mem _ y)
    rw [add_sub_cancel_right]

theorem IntermediateField.adjoin_simple_add {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (y : F) : adjoin F {x + algebraMap F E y} = adjoin F {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact add_mem (mem_adjoin_simple_self F x) (algebraMap_mem _ y)
  · rw [adjoin_simple_le_iff]
    convert IntermediateField.sub_mem _ (mem_adjoin_simple_self F _) (algebraMap_mem _ y)
    rw [eq_sub_iff_add_eq]

theorem IntermediateField.adjoin_simple_mul {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (y : F) (hy : y ≠ 0) : adjoin F {x * algebraMap F E y} = adjoin F {x} := by
  apply le_antisymm
  · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact mul_mem (mem_adjoin_simple_self F x) (algebraMap_mem _ y)
  · rw [adjoin_simple_le_iff]
    convert IntermediateField.div_mem _ (mem_adjoin_simple_self F _) (algebraMap_mem _ y)
    rw [mul_div_cancel_right₀ x (by rwa [map_ne_zero])]

/-! ### MulEquiv / AlgHom / AlgEquiv -/

@[to_additive (attr := simp)]
theorem MulEquiv.ofBijective_symm_apply_apply {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] (f : F) (hf : Function.Bijective f) (a : M) :
    (ofBijective f hf).symm (f a) = a := (symm_apply_eq (ofBijective f hf)).mpr rfl

/-! ### Coprime exponent power extraction -/

/-- If `x ^ m = y ^ n` with `m` and `n` coprime and `x ≠ 0`, then `x` is itself an `n`-th power. -/
theorem exists_eq_pow_of_pow_eq_pow_of_coprime {G : Type*} [CommGroupWithZero G] {m n : ℕ}
    (hmn : Nat.Coprime m n) {x y : G} (hx : x ≠ 0) (h : x ^ m = y ^ n) :
    ∃ z : G, z ≠ 0 ∧ x = z ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [(Nat.coprime_zero_right _).mp hmn, pow_one, pow_zero] at h
    exact ⟨1, one_ne_zero, by rw [pow_zero, h]⟩
  · have hy : y ≠ 0 := fun hy ↦ pow_ne_zero m hx (by rw [h, hy, zero_pow hn])
    refine ⟨y ^ Int.gcdA m n * x ^ Int.gcdB m n,
      mul_ne_zero (zpow_ne_zero _ hy) (zpow_ne_zero _ hx), ?_⟩
    rw [mul_pow, ← zpow_natCast, zpow_comm, zpow_natCast, ← h, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hx, mul_comm _ (n : ℤ), ← Int.gcd_eq_gcd_ab,
      Int.gcd_natCast_natCast, hmn, Nat.cast_one, zpow_one]

/-! ### Order of powers -/

/-- Analogue of `IsPrimitiveRoot.pow` for `orderOf`: if `orderOf x = a * b` then
`orderOf (x ^ a) = b`. -/
theorem orderOf_pow_of_orderOf_eq_mul {G : Type*} [Monoid G] {x : G} {a b : ℕ}
    (hn : 0 < orderOf x) (h : orderOf x = a * b) : orderOf (x ^ a) = b := by
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hn.ne')
  rw [orderOf_pow_of_dvd ha ⟨b, h⟩, h, Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero ha)]

/-- The `zpow` version of `orderOf_pow_dvd`: `orderOf (x ^ n)` divides `orderOf x` for `n : ℤ`. -/
theorem orderOf_zpow_dvd {G : Type*} [Group G] (x : G) (n : ℤ) :
    orderOf (x ^ n) ∣ orderOf x := by
  rw [← orderOf_pow_natAbs]
  exact orderOf_pow_dvd _

/-! ### Cyclic groups in a product -/

/-- The group-theoretic heart of the tame Abhyankar lemma: a cyclic group that embeds into a product
`A × B` of finite groups has order dividing `Nat.lcm (Nat.card A) (Nat.card B)`. (A generator maps to
some `(a, b)` of order `lcm (orderOf a) (orderOf b)`, and each component order divides the
corresponding cardinality.) -/
theorem card_dvd_lcm_of_isCyclic_of_injective {G A B : Type*} [Group G] [Group A] [Group B]
    [IsCyclic G] {f : G →* A × B} (hf : Function.Injective f) :
    Nat.card G ∣ Nat.lcm (Nat.card A) (Nat.card B) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  rw [← Subgroup.card_top, ← (Subgroup.eq_top_iff' _).mpr hg, Nat.card_zpowers g,
    ← orderOf_injective f hf g, Prod.orderOf]
  exact Nat.lcm_dvd ((orderOf_dvd_natCard _).trans (Nat.dvd_lcm_left _ _))
      ((orderOf_dvd_natCard _).trans (Nat.dvd_lcm_right _ _))

/-- Subgroup form of `card_dvd_lcm_of_isCyclic_of_injective`: a cyclic group with two normal
subgroups of trivial intersection has order dividing the lcm of the two quotient orders. -/
theorem card_dvd_lcm_of_isCyclic_of_inf_eq_bot {G : Type*} [Group G] [IsCyclic G]
    {H₁ H₂ : Subgroup G} [H₁.Normal] [H₂.Normal] (h : H₁ ⊓ H₂ = ⊥) :
    Nat.card G ∣ Nat.lcm H₁.index H₂.index :=
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
`subgroupOfEquivOfLe`; this composes two copies of it through `↥(A ⊓ B)`. -/
@[to_additive /-- `A.addSubgroupOf B` and `B.addSubgroupOf A` are isomorphic (both realize `A ⊓ B`). -/]
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

/-! ### MISC -/

@[simp]
theorem MulAut.conjNormal_apply_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G]
    {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    conjNormal g h = h := by
  rw [Subtype.ext_iff, conjNormal_apply, mul_comm', inv_mul_cancel_left]

@[simp]
theorem MulAut.conjNormal_symm_apply_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G]
    {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    (MulAut.conjNormal g).symm h = h := by
  rw [MulEquiv.symm_apply_eq, conjNormal_apply_of_isMulCommutative]

/-! ### Characters: order and quotient by the kernel -/

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

@[to_additive]
theorem Subgroup.index_ker_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) :
    f.ker.index = Nat.card H := by
  have := Subgroup.index_ker f
  rwa [MonoidHom.range_eq_top_of_surjective _ hf, Subgroup.card_top] at this

open Finset Subgroup in
theorem isCyclic_of_subgroup_card_injective {G : Type*} [Group G] [Finite G]
    (h : ∀ H K : Subgroup G, Nat.card H = Nat.card K → H = K) :
    IsCyclic G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have key (d : ℕ) : Finset.card {x : G | orderOf x = d} ≤ d.totient := by
    obtain h | ⟨x, hx⟩  := (univ.filter fun a : G ↦ orderOf a = d).eq_empty_or_nonempty
    · simp [h]
    · obtain ⟨-, hxd⟩ := mem_filter.mp hx
      have h' {y} (hy : orderOf y = d) : y ∈ zpowers x := by
        rw [← zpowers_le]
        exact le_of_eq <| h _ _ (by rw [Nat.card_zpowers, Nat.card_zpowers, hxd, hy])
      rw [← IsCyclic.card_orderOf_eq_totient (α := zpowers x) (by rw [Fintype.card_zpowers, hxd]),
        ← Finset.card_image_of_injective _ Subtype.val_injective]
      apply Finset.card_mono <|
        fun y hy ↦ mem_image.mpr ⟨⟨y, h' (by simpa using hy)⟩, by simpa using hy, rfl⟩
  refine isCyclic_of_card_pow_eq_one_le fun n hn ↦ ?_
  calc
    _ = ∑ d ∈ n.divisors, (univ.filter fun a ↦ orderOf a = d).card :=
        (sum_card_orderOf_eq_card_pow_eq_one hn.ne').symm
    _ ≤ ∑ d ∈ n.divisors, d.totient := Finset.sum_le_sum fun d _ ↦ key d
    _ = n := Nat.sum_totient n

/-- A finite group is cyclic iff its subgroups are determined by their cardinality. The forward
direction is `IsCyclic.subgroup_eq_subgroup_iff`; the converse is
`isCyclic_of_subgroup_card_injective`. -/
theorem isCyclic_iff_subgroup_card_injective {G : Type*} [Group G] [Finite G] :
    IsCyclic G ↔ ∀ H K : Subgroup G, Nat.card H = Nat.card K → H = K :=
  ⟨fun _ _ _ => IsCyclic.subgroup_eq_subgroup_iff.mpr, isCyclic_of_subgroup_card_injective⟩

/-- A finite non-cyclic abelian `p`-group has two distinct subgroups of index `p`. -/
theorem IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic {G : Type*} [CommGroup G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : IsPGroup p G) (hnc : ¬ IsCyclic G) :
  ∃ H₁ H₂ : Subgroup G, H₁.index = p ∧ H₂.index = p ∧ H₁ ≠ H₂ := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have : Nonempty ι := by
    contrapose! hnc
    exact e.isCyclic.mpr inferInstance
  have : Nontrivial ι := by
    contrapose! hnc
    have : Unique ι := uniqueOfSubsingleton Classical.ofNonempty
    exact e.isCyclic.mpr <| (MulEquiv.piUnique _).isCyclic.mpr inferInstance
  have hpn {i} : p ∣ n i := by
    rsuffices ⟨k, hk⟩ : ∃ k, n i = p ^ k := by
      let g := Pi.evalAddMonoidHom (fun i ↦ ZMod (n i)) i
      have hg : Function.Surjective g := fun x ↦ ⟨Pi.single i x, by simp [g]⟩
      have := Subgroup.index_ker_of_surjective (g.toMultiplicative.comp e.toMonoidHom) (hg.comp e.surjective)
      rw [← Nat.card_congr Multiplicative.ofAdd, Nat.card_zmod] at this
      exact this ▸ IsPGroup.index hG _
    have : k ≠ 0 := fun h ↦ (hn i).ne' <| (by rwa [h, pow_zero] at hk)
    simp [hk, this]
  obtain ⟨j, k, hij⟩ := exists_pair_ne ι
  let g₁ : ((i : ι) → ZMod (n i)) →+ ZMod (n j) × ZMod (n k) :=
    AddMonoidHom.prod (Pi.evalAddMonoidHom _ j) (Pi.evalAddMonoidHom _ k)
  have hg₁ : Function.Surjective g₁ :=
    fun x ↦ ⟨Pi.single j x.1 + Pi.single k x.2, by ext <;> simp [g₁, hij]⟩
  let g₂ (i) : ZMod (n i) →+ ZMod p := (ZMod.castHom hpn (ZMod p)).toAddMonoidHom
  have hg₂ (i) : Function.Surjective (g₂ i) := ZMod.castHom_surjective hpn
  let g₃ : ((i : ι) → ZMod (n i)) →+ ZMod p × ZMod p := ((g₂ j).prodMap (g₂ k)).comp g₁
  have hg₃ : Function.Surjective g₃ := ((hg₂ j).prodMap (hg₂ k)).comp hg₁
  let g := g₃.toMultiplicative.comp e.toMonoidHom
  have hg : Function.Surjective g := by
    simp only [g, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp]
    exact hg₃.comp e.surjective
  refine ⟨((AddMonoidHom.fst _ _).toMultiplicative.comp g).ker,
    ((AddMonoidHom.snd _ _).toMultiplicative.comp g).ker, ?_, ?_, ?_⟩
  · rw [Subgroup.index_ker_of_surjective, ← Nat.card_congr Multiplicative.ofAdd, Nat.card_zmod]
    exact Prod.fst_surjective.comp hg
  · rw [Subgroup.index_ker_of_surjective, ← Nat.card_congr Multiplicative.ofAdd, Nat.card_zmod]
    exact Prod.snd_surjective.comp hg
  · obtain ⟨y, hy⟩ := hg <| Multiplicative.ofAdd (0, 1)
    exact ne_of_mem_of_not_mem' (a := y) (by simp [hy]) (by simp [hy])

end

end
