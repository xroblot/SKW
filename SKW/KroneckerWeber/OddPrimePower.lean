module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.ZMod.UnitsCyclic

public import SKW.KroneckerWeber.Basic
public import SKW.KroneckerWeber.ClassGroup
public import SKW.KroneckerWeber.Reduction
public import SKW.Prereqs.Unramified
public import SKW.Prereqs.NumberField
public import SKW.Prereqs.IntermediateFields

@[expose] public section

/-!
# Kronecker-Weber for odd prime power cyclic extensions

Every cyclic extension of `ℚ` of odd prime power degree `pᵐ` unramified outside `p` is
contained in `ℚ(ζ_{p^{m+1}})`.

The key step is `prop_kw_exponent_p` (the degree `p` case), proved here via the class-group
argument of `ClassGroup.lean`. The
induction uses `kw_cyclic_compositum`: if the candidate cyclotomic subfield `K'` of degree `pᵐ`
and `K` have non-cyclic compositum, one obtains a `(ℤ/pℤ)²`-extension unramified outside `p`,
contradicting `prop_kw_exponent_p`.
-/

open NumberField Ideal IntermediateField IsCyclotomicExtension

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]


set_option backward.isDefEq.respectTransparency false in
open IntermediateField Polynomial in
/-- Every cyclic extension of `ℚ` of prime degree `p` (odd) unramified outside `p` is contained in
`ℚ(ζ_{p²}) = ℚ⟮ξ⟯`. Here `K`, `ℚ⟮ζ⟯` stay in `A`; the Kummer/class-group work runs on the tower
`ℚ → ↥ℚ⟮ζ⟯ → ↥(K ⊔ ℚ⟮ζ⟯)`, with no restriction of `K`. -/
theorem prop_kw_exponent_p (hp' : Odd p) {A : Type*} [Field A] [CharZero A] {ξ : A}
    (hξ : IsPrimitiveRoot ξ (p ^ 2)) (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K]
    [hCK : IsCyclic Gal(K/ℚ)] (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p) :
    K ≤ ℚ⟮ξ⟯ := by
  let ζ : A := ξ ^ p
  have hζ : IsPrimitiveRoot ζ p := hξ.pow (NeZero.pos _) (by rw [pow_two])
  have : IsCyclotomicExtension {p} ℚ ℚ⟮ζ⟯ := hζ.adjoinSimple_isCyclotomicExtension p ℚ A
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {p} ℚ ℚ⟮ζ⟯
  have : IsAbelianGalois ℚ K := IsAbelianGalois.of_isCyclic ℚ K
  have : IsAbelianGalois ℚ ℚ⟮ζ⟯ := isAbelianGalois {p} ℚ ℚ⟮ζ⟯
  let M : IntermediateField ℚ A := K ⊔ ℚ⟮ζ⟯
  letI : Algebra ℚ⟮ζ⟯ M := (inclusion (le_sup_right : ℚ⟮ζ⟯ ≤ M)).toAlgebra
  haveI : IsScalarTower ℚ ℚ⟮ζ⟯ M :=
    IsScalarTower.of_algebraMap_eq fun x => ((inclusion (le_sup_right : ℚ⟮ζ⟯ ≤ M)).commutes x).symm
  have hMram : UnramifiedOutside M p := unramifiedOutside_sup p K ℚ⟮ζ⟯ hKram
    (unramifiedOutside_of_isCyclotomicExtension p)
  have hζdeg : Module.finrank ℚ ℚ⟮ζ⟯ = p - 1 :=
    Nat.totient_prime hp.out ▸ IsCyclotomicExtension.Rat.finrank p ℚ⟮ζ⟯
  have hMdeg : Module.finrank ℚ ↥M = p * (p - 1) := by
    have hinf : Module.finrank ℚ ↥(K ⊓ ℚ⟮ζ⟯) = 1 := by
      have hc : p.Coprime (p - 1) := by have := hp.out.one_le; aesop
      have h₁ : Module.finrank ℚ ↑(K ⊓ ℚ⟮ζ⟯) ∣ p := by
        rw [← hK]; exact finrank_dvd_of_le_right inf_le_left
      have h₂ : Module.finrank ℚ ↑(K ⊓ ℚ⟮ζ⟯) ∣ p - 1 := by
        rw [← hζdeg]; exact finrank_dvd_of_le_right inf_le_right
      exact Nat.dvd_one.mp (hc ▸ Nat.dvd_gcd h₁ h₂)
    have := finrank_sup_mul_finrank_inf_eq K ℚ⟮ζ⟯
    rwa [hinf, mul_one, hK, hζdeg] at this
  obtain ⟨hGal, hCyc, hrF⟩ := kw_kummer₀ p (F := ℚ⟮ζ⟯) (L := M) hMdeg
  obtain ⟨μ, hμ, hS⟩ := kw_kummer p ↥ℚ⟮ζ⟯ hrF
  have hIrr : Irreducible (X ^ p - C (algebraMap (𝓞 ℚ⟮ζ⟯) ℚ⟮ζ⟯ μ)) := by
    rw [X_pow_sub_C_irreducible_iff_of_prime hp.out]
    intro b hb
    have := hS.splits_iff.mp (X_pow_sub_C_splits_of_isPrimitiveRoot (zeta_spec p ℚ ↥ℚ⟮ζ⟯) hb)
    rw [eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one, hrF] at this
    exact hp.out.ne_one this
  obtain ⟨𝔞, h𝔞₀, h𝔞⟩ := kw_mu_pth_power_ideal p ℚ⟮ζ⟯ hrF hμ hIrr hMram hp'
  have hcyc : IsCyclotomicExtension {p ^ 2} ℚ M :=
    kw_unit_root_of_unity p ℚ⟮ζ⟯ hrF hμ hIrr hp' h𝔞₀ h𝔞
  have hMeq : M = ℚ⟮ξ⟯ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin (p ^ 2) ℚ A M hξ).mp hcyc
  exact le_sup_left.trans hMeq.le

set_option backward.isDefEq.respectTransparency false in
theorem prop_kw_exponent_p_eq (hp' : Odd p) {A : Type*} [Field A] [CharZero A] {ξ : A}
    (hξ : IsPrimitiveRoot ξ (p ^ 2)) (K₁ K₂ : IntermediateField ℚ A) [NumberField K₁] [IsGalois ℚ K₁]
    [hC₁ : IsCyclic Gal(K₁/ℚ)] (hK₁ : Module.finrank ℚ K₁ = p) (hKram₁ : UnramifiedOutside K₁ p)
    [NumberField K₂] [IsGalois ℚ K₂] [hC₂ : IsCyclic Gal(K₂/ℚ)] (hK₂ : Module.finrank ℚ K₂ = p)
    (hKram₂ : UnramifiedOutside K₂ p) :
    K₁ = K₂ := by
  have : IsCyclotomicExtension {p ^ 2} ℚ ℚ⟮ξ⟯ := hξ.adjoinSimple_isCyclotomicExtension (p ^ 2) ℚ A
  have : NumberField ℚ⟮ξ⟯ := IsCyclotomicExtension.numberField {p ^ 2} ℚ _
  have h₁ : K₁ ≤ ℚ⟮ξ⟯ := prop_kw_exponent_p p hp' hξ K₁ hK₁ hKram₁
  have h₂ : K₂ ≤ ℚ⟮ξ⟯ := prop_kw_exponent_p p hp' hξ K₂ hK₂ hKram₂
  let : Algebra K₁ ↑(K₁ ⊔ K₂) := (inclusion le_sup_left).toAlgebra
  suffices Module.finrank ℚ K₁ = Module.finrank ℚ ↑(K₁ ⊔ K₂) by
      rw [← eq_iff_finrank_eq_of_le le_sup_left, left_eq_sup] at this
      rw [eq_comm]
      exact eq_of_le_of_finrank_eq this (by rw [hK₁, hK₂])
  rw [← Module.finrank_mul_finrank ℚ K₁ ↑(K₁ ⊔ K₂), left_eq_mul₀ Module.finrank_pos.ne']
  have h_ineq := finrank_le_of_le_right <| sup_le h₁ h₂
  rw [Rat.finrank (p ^ 2) ℚ⟮ξ⟯, ← Module.finrank_mul_finrank ℚ K₁, hK₁,
    Nat.totient_prime_pow hp.out (by simp), Nat.add_one_sub_one, pow_one,
    Nat.mul_le_mul_left_iff (NeZero.pos p)] at h_ineq
  have h_div := finrank_sup_dvd_mul_of_isGalois K₁ K₂
  rw [← Module.finrank_mul_finrank ℚ K₁, Nat.mul_dvd_mul_iff_left Module.finrank_pos, hK₂,
    Nat.dvd_prime hp.out] at h_div
  exact h_div.resolve_right fun h ↦ by grind [hp.out.ne_zero]

variable [hp' : Fact (Odd p)]

set_option backward.isDefEq.respectTransparency false in
open IntermediateField in
/-- Every cyclic extension of `ℚ` of odd prime power degree `pᵐ` unramified outside `p` is
cyclotomic: contained in `ℚ(ζ_{p^{m+1}}) = ℚ⟮ξ (p^(m+1))⟯` inside the ambient field `A`. -/
theorem prop_kw_odd_prime_power {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ) (hm : 0 < m) (K : IntermediateField ℚ A)
    [NumberField K] [IsAbelianGalois ℚ K] (hK : Module.finrank ℚ K = p ^ m)
    (hKram : UnramifiedOutside K p) :
    K ≤ ℚ⟮ξ (p ^ (m + 1))⟯ := by
  let C : IntermediateField ℚ A := ℚ⟮ξ (p ^ (m + 1))⟯
  have hC : IsCyclotomicExtension {p ^ (m + 1)} ℚ C :=
    (hξ (p ^ (m + 1))).adjoinSimple_isCyclotomicExtension _ ℚ A
  have : IsAbelianGalois ℚ C := isAbelianGalois {p ^ (m + 1)} ℚ C
  have : NumberField C := IsCyclotomicExtension.numberField {p ^ (m + 1)} ℚ C
  obtain ⟨K', hK'₁, hK'₂, hK'₃, hK'₄⟩ :
      ∃ K' : IntermediateField ℚ A, K' ≤ C ∧ Module.finrank ℚ K' = p ^ m ∧
        IsCyclic Gal(K'/ℚ) ∧ UnramifiedOutside K' p := by
    have : IsCyclic Gal(C/ℚ) := by
      rw [(Rat.galEquivZMod (p ^ (m + 1)) C).isCyclic]
      exact ZMod.isCyclic_units_of_prime_pow _ hp.out (by grind [hp'.out]) _
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(C/ℚ))
    have hC : Nat.card Gal(C/ℚ) = p ^ m * (p - 1) := by
      rw [IsGalois.card_aut_eq_finrank, Rat.finrank (p ^ (m + 1)),
        Nat.totient_prime_pow hp.out (by positivity), add_tsub_cancel_right]
    refine ⟨lift (fixedField (Subgroup.zpowers (σ ^ (p ^ m)))), lift_le _, ?_, ?_, ?_⟩
    · rw [finrank_lift, fixedField, IsGaloisGroup.finrank_fixedPoints_eq_index_subgroup,
        Subgroup.index_eq_iff_card_mul_eq_card, Nat.card_zpowers,
        orderOf_pow_of_orderOf_eq_mul (orderOf_pos σ) (by rw [hσ, hC]),
        IsGalois.card_aut_eq_finrank, Rat.finrank (p ^ (m + 1)),
        Nat.totient_prime_pow hp.out (by positivity), add_tsub_cancel_right, mul_comm]
    · rw [(liftAlgEquiv _).symm.autCongr.isCyclic, ← (IsGalois.normalAutEquivQuotient _).isCyclic]
      apply isCyclic_of_surjective _ (QuotientGroup.mk'_surjective _)
    · intro q hq hqp
      have : Fact q.Prime := ⟨hq⟩
      apply Algebra.IsUnramifiedIn.of_algEquiv <|
        RingOfIntegers.mapIntAlgEquiv (liftAlgEquiv _).toRingEquiv
      refine Algebra.IsUnramifiedIn.tower_bot (T := 𝓞 C) fun Q hQ₁ hQ₂ ↦
        ramificationIdx'_eq_one_iff.mp ?_
      rw [Rat.ramificationIdx_eq_of_not_dvd q (m := p ^ (m + 1))]
      intro h
      exact hqp <| (Nat.prime_dvd_prime_iff_eq hq hp.out).mp <| hq.dvd_of_dvd_pow h
  have : NumberField K' :=
    let : Algebra K' C := (inclusion hK'₁).toAlgebra
    NumberField.of_tower ℚ C _
  have : IsAbelianGalois ℚ K' := by
    have : Algebra K' C := (inclusion hK'₁).toAlgebra
    exact IsAbelianGalois.tower_bot ℚ K' C
  have hCyc : IsCyclic Gal(↑(K ⊔ K')/ℚ) := by
    have : IsAbelianGalois ℚ ↑(K ⊔ K') := IsAbelianGalois.sup K K'
    let : CommGroup Gal(↑(K ⊔ K')/ℚ) := IsMulCommutative.instCommGroup
    by_contra! hCyc
    have hP : IsPGroup p Gal(↑(K ⊔ K')/ℚ) := by
      refine IsPGroup.iff_card.mpr ?_
      rw [IsGalois.card_aut_eq_finrank]
      have := finrank_sup_dvd_mul_of_isGalois K K'
      rw [hK, hK'₂, ← pow_add, Nat.dvd_prime_pow hp.out] at this
      obtain ⟨k, _, hk⟩ := this
      exact ⟨k, hk⟩
    obtain ⟨H₁, H₂, hind₁, hind₂, h₁₂⟩ := IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic hP hCyc
    let K₁ := fixedField H₁
    let K₂ := fixedField H₂
    suffices K₁ = K₂ by
      refine h₁₂ ?_
      simpa [K₁, K₂, fixingSubgroup_fixedField] using congr_arg (fixingSubgroup · ) this
    apply lift_injective
    have hK₁ : Module.finrank ℚ K₁ = p := by
      rw [← IsGalois.card_aut_eq_finrank,
        ← Nat.card_congr (IsGalois.normalAutEquivQuotient _).toEquiv, ← Subgroup.index, hind₁]
    have hK₂ : Module.finrank ℚ K₂ = p := by
      rw [← IsGalois.card_aut_eq_finrank,
        ← Nat.card_congr (IsGalois.normalAutEquivQuotient _).toEquiv, ← Subgroup.index, hind₂]
    have hcyc₁ : IsCyclic Gal(K₁/ℚ) :=
      isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, hK₁])
    have hcyc₂ : IsCyclic Gal(K₂/ℚ) :=
      isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, hK₂])
    apply prop_kw_exponent_p_eq p hp'.out (hξ (p ^ 2))
    · rwa [finrank_lift]
    · apply UnramifiedOutside.of_algEquiv p (liftAlgEquiv _)
      exact UnramifiedOutside.tower_bot p (unramifiedOutside_sup p K K' hKram hK'₄)
    · rwa [finrank_lift]
    · apply UnramifiedOutside.of_algEquiv p (liftAlgEquiv _)
      exact UnramifiedOutside.tower_bot p (unramifiedOutside_sup p K K' hKram hK'₄)
  have hKK' : K ≤ K' := by
    have := kw_cyclic_compositum ↑(K ⊔ K') (K.restrict le_sup_left) (K'.restrict le_sup_right)
      (by rw [finrank_restrict, finrank_restrict, hK, hK'₂])
    rwa [restrict_le_restrict_iff] at this
  exact hKK'.trans hK'₁

end

end

/- Superseded by the tower-chain version below (renamed to `prop_kw_exponent_p`):
set_option backward.isDefEq.respectTransparency false in
open IntermediateField Polynomial in
/-- Every cyclic extension of `ℚ` of prime degree `p` (odd) unramified outside `p` is contained
in `ℚ(ζ_{p²}) = ℚ⟮ξ⟯`. -/
theorem prop_kw_exponent_p (hp' : Odd p) {A : Type*} [Field A] [CharZero A] {ξ : A}
    (hξ : IsPrimitiveRoot ξ (p ^ 2)) (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K]
    [hCK : IsCyclic Gal(K/ℚ)] (hK : Module.finrank ℚ K = p) (hKram : UnramifiedOutside K p) :
    K ≤ ℚ⟮ξ⟯ := by
  let ζ : A := ξ ^ p
  have hζ : IsPrimitiveRoot ζ p := hξ.pow (NeZero.pos _) (by rw [pow_two])
  have : IsCyclotomicExtension {p} ℚ ℚ⟮ζ⟯ :=
    hζ.adjoinSimple_isCyclotomicExtension p ℚ A
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {p} ℚ ℚ⟮ζ⟯
  let M : IntermediateField ℚ A := K ⊔ ℚ⟮ζ⟯
  let F : IntermediateField ℚ M := (ℚ⟮ζ⟯).restrict le_sup_right
  let K' : IntermediateField ℚ M := K.restrict le_sup_left
  have : IsCyclotomicExtension {p} ℚ F :=
    IsCyclotomicExtension.equiv {p} ℚ ℚ⟮ζ⟯ <| restrict_algEquiv le_sup_right
  have : IsAbelianGalois ℚ F := isAbelianGalois {p} ℚ F
  have : IsGalois ℚ K' := IsGalois.of_algEquiv <| restrict_algEquiv le_sup_left
  have : IsCyclic Gal(K'/ℚ) := (AlgEquiv.autCongr (restrict_algEquiv le_sup_left)).isCyclic.mp hCK
  have : IsAbelianGalois ℚ K' := IsAbelianGalois.of_isCyclic ℚ K'
  have htop : K' ⊔ F = ⊤ :=
    lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_top])
  have : IsGalois F M := IsGalois.sup_right (F := ℚ) K' F htop
  have : IsCyclic Gal(M/F) := by
    apply isCyclic_of_injective <| restrictRestrictAlgEquivMapHom ℚ K' F M
    exact restrictRestrictAlgEquivMapHom_injective K' F htop
  have : IsAbelianGalois ℚ (⊤ : IntermediateField ℚ M) := by
    rw [← htop]
    exact IsAbelianGalois.sup K' F
  have : IsAbelianGalois ℚ M := IsAbelianGalois.of_algHom topEquiv.symm.toAlgHom
  have hK' : Module.finrank ℚ K' = p := by
    rw [← hK, ← (restrict_algEquiv le_sup_left).toLinearEquiv.finrank_eq]
  have hrF : Module.finrank F M = p := (kw_kummer₀ p F K' hK' htop).2.2
  have hK'ram : UnramifiedOutside K' p := fun q hq hqp ↦
    (hKram q hq hqp).of_algEquiv
      ((RingOfIntegers.mapAlgEquiv (restrict_algEquiv le_sup_left)).restrictScalars ℤ)
  obtain ⟨μ, hμ, hS⟩ := kw_kummer p F K' hrF hK'
  have hIrr : Irreducible (X ^ p - C (algebraMap (𝓞 F) F μ)) := by
    rw [X_pow_sub_C_irreducible_iff_of_prime hp.out]
    intro b hb
    have := hS.splits_iff.mp (X_pow_sub_C_splits_of_isPrimitiveRoot (zeta_spec p ℚ F) hb)
    rw [eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one, hrF] at this
    exact hp.out.ne_one this
  have hMram : UnramifiedOutside M p := kw_kummer' p F K' hK'ram htop
  obtain ⟨𝔞, h𝔞₀, h𝔞⟩ := kw_mu_pth_power_ideal p F hrF hμ hIrr hMram hp'
  have hcyc : IsCyclotomicExtension {p ^ 2} ℚ M :=
    kw_unit_root_of_unity p F hrF hμ hIrr hp' K' hK' hK'ram hS h𝔞₀ h𝔞
  have hMeq : M = ℚ⟮ξ⟯ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin (p ^ 2) ℚ A M hξ).mp hcyc
  exact le_sup_left.trans hMeq.le
-/
