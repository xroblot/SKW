module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Data.Nat.Factors
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

public import SKW.KroneckerWeber.Basic
public import SKW.KroneckerWeber.Reduction
public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.CMField
public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.ZModUnits

set_option linter.style.header false

@[expose] public section

/-!
# Kronecker-Weber for 2-power cyclic extensions

The `p = 2` case of the reduction to prime power degree, handled by **Lemmermeyer's argument**
(Prop. 1.5). Unlike the odd case (`prop_kw_odd_prime_power`), this needs **no** Kummer/class-group
machinery: `ℚ(ζ_{2^n})/ℚ` is not cyclic (`(ℤ/2^n)ˣ ≅ ℤ/2 × ℤ/2^{n-2}`), so the odd-case template
"unique subfield of each degree" fails; instead the argument is elementary, driven by the
classification of quadratics and the compositum comparison.

## Structure

- `kw_2_quadratic_discr`: a quadratic extension of `ℚ` unramified outside `2` has discriminant
  `-8`, `-4` or `8` (the three fields are `ℚ(√-2)`, `ℚ(i)`, `ℚ(√2)`, all inside `ℚ(ζ_8)`).
- `prop_kw_2_quadratic_real_unique`: there is a *unique* totally real quadratic extension of `ℚ`
  unramified outside `2` (namely `ℚ(√2) = ℚ(ζ_8)⁺`). This is the pigeonhole that forces cyclicity of
  the relevant compositum in the real case.
- `prop_kw_2_power_real`: the **real case** — a totally real cyclic `2^m` extension unramified
  outside `2` is contained in `ℚ(ζ_{2^{m+2}})`.
- `prop_kw_2_power`: the **general case**, reduced to the real case via the CM field `K(i)`.

The engines are `kw_cyclic_compositum`, the non-cyclic-`2`-group fact
`IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic`, and Mathlib's CM-field API
(`maximalRealSubfield`/`complexConj`, with cyclotomic fields CM via
`IsCyclotomicExtension.Rat.isCMField`).
-/

open NumberField NumberField.QuadraticField Ideal

noncomputable section

/-- A quadratic field unramified outside `2` has discriminant `-8`, `-4` or `8`, that is, it is
`ℚ(√-2)`, `ℚ(i)` or `ℚ(√2)`. -/
theorem kw_2_quadratic_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hKram : UnramifiedOutside K 2) :
    NumberField.discr K = -8 ∨ NumberField.discr K = -4 ∨ NumberField.discr K = 8 := by
  have h_main {p : ℕ} : p.Prime → (p : ℤ) ∣ discr K → p = 2 := by
    intro hp₁ hp₂
    contrapose! hp₂
    exact (not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp₁)).mpr
      <| hKram p hp₁ hp₂
  have hfund : Int.IsFundamentalDiscr (discr K) := isFundamentalDiscr_discr K hK
  have hKne : (discr K).natAbs ≠ 1:= by
    grind [NumberField.abs_discr_gt_two (K := K) (hK ▸ one_lt_two)]
  obtain h | h := hfund.emod_four_eq_zero_or_one
  · obtain ⟨m, hm⟩ := Int.dvd_iff_emod_eq_zero.mpr h
    simp only [hm, Int.isFundamentalDiscr_four_mul] at *
    have : m.natAbs = 1 ∨ m.natAbs = 2 := by
      rw [← Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hfund.1)]
      have : m.natAbs.primeFactors ⊆ {2} := by
        refine Finset.subset_singleton_iff'.mpr fun p hp ↦ ?_
        obtain ⟨hp₁, hp₂, -⟩ := Nat.mem_primeFactors.mp hp
        exact h_main hp₁ <| Int.dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hp₂)
      grind [Finset.subset_singleton_iff]
    grind
  · have hKo : Odd (discr K) := by
      rw [Int.odd_iff, ← Int.emod_emod_of_dvd _ (by norm_num : (2 : ℤ) ∣ 4), h, Int.one_emod_two]
    obtain ⟨p, hp₁, hp₂, hp₃⟩ : ∃ (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (p : ℤ) ∣ discr K := by
      obtain ⟨p, hp₁, hp₃⟩ := Nat.exists_prime_and_dvd hKne
      rw [← Int.natCast_dvd] at  hp₃
      refine ⟨p, hp₁, ?_, hp₃⟩
      contrapose! hp₃
      rw [hp₃, Nat.cast_ofNat]
      exact Int.not_two_dvd_iff_odd.mpr hKo
    exact False.elim (hp₂ <| h_main hp₁ hp₃)

/- No longer used: `prop_kw_2_quadratic_real_unique` now goes through the discriminant
(`kw_2_quadratic_discr` and `nonempty_algEquiv_iff_discr_eq`) rather than through the inclusion in
`ℚ(ζ_8)`. Kept here, commented out, since it is the classification statement the blueprint
advertises.

open IntermediateField in
/-- The quadratic extensions of `ℚ` unramified outside `2` are exactly `ℚ(i)`, `ℚ(√-2)`, `ℚ(√2)`,
all contained in `ℚ(ζ_8) = ℚ⟮ξ 8⟯`. (Proof: by `kw_2_quadratic_discr` the discriminant of `K` is
`-8`, `-4` or `8`, so `K` is `ℚ(√-2)`, `ℚ(i)` or `ℚ(√2)` respectively; and `ζ_8` supplies
`√-2 = ζ_8 + ζ_8³`, `i = ζ_8²` and `√2 = ζ_8 + ζ_8⁻¹`.) -/
theorem prop_kw_2_quadratic {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K]
    (hK : Module.finrank ℚ K = 2) (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ 8⟯ := by
  set ζ := ξ 8
  rsuffices ⟨y, hy₁, hy₂⟩ : ∃ y ∈ ℚ⟮ζ⟯, (y : A) ^ 2 = discr K
  · have h₃ : y ∈ K := by
      obtain ⟨x, hx⟩ := QuadraticField.exists_sq_eq_discr K hK
      replace hx := congr_arg ((↑) : K → A) hx
      obtain rfl | rfl := eq_or_eq_neg_of_sq_eq_sq _ _ <| hy₂.trans hx.symm
      · exact SetLike.coe_mem x
      · exact neg_mem_iff.mpr <| SetLike.coe_mem x
    have h₄ : IsIntegral ℚ y := (IsIntegral.of_finite ℚ (⟨y, h₃⟩ : K)).map K.val
    have h₅ : ℚ⟮y⟯ = K := by
      refine eq_of_le_of_finrank_le (adjoin_simple_le_iff.mpr h₃) ?_
      rw [hK, two_le_finrank_adjoin_simple_iff _ h₄]
      intro h
      refine not_isSquare_discr K hK ?_
      obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp h
      rw [← Rat.isSquare_intCast_iff]
      refine ⟨r, ?_⟩
      apply FaithfulSMul.algebraMap_injective ℚ A
      rw [map_intCast, ← hy₂, pow_two, map_mul]
    exact h₅ ▸ adjoin_simple_le_iff.mpr hy₁
  · have hζ₀ : ζ ≠ 0 := (hξ 8).ne_zero (by norm_num)
    have hζ₁ : (ζ ^ 2) ^ 2 = -1 := by
      rw [← pow_mul]
      exact IsPrimitiveRoot.eq_neg_one_of_two_right <| (hξ 8).pow (by positivity) (by norm_num)
    have hζ₂ : ζ ^ 2 + ζ⁻¹ ^ 2 = 0 := by grind
    obtain hd | hd | hd := kw_2_quadratic_discr K hK hKram
    · refine ⟨2 * (ζ - ζ⁻¹), by aesop, ?_⟩
      rw [mul_pow, sub_sq, sub_add_eq_add_sub, hζ₂, zero_sub, mul_inv_cancel_right₀ hζ₀, hd]
      norm_num
    · refine ⟨2 * ζ ^ 2, by aesop, ?_⟩
      rw [mul_pow, hζ₁, hd]
      norm_num
    · refine ⟨2 * (ζ + ζ⁻¹), by aesop, ?_⟩
      rw [mul_pow, add_sq, add_right_comm, hζ₂, zero_add, mul_inv_cancel_right₀ hζ₀, hd]
      norm_num
-/

open IntermediateField in
/-- Uniqueness of the real quadratic: any two *totally real* quadratic extensions of `ℚ` unramified
outside `2` coincide (both equal `ℚ(√2) = ℚ(ζ_8)⁺`). By `kw_2_quadratic_discr` both discriminants
are `-8`, `-4` or `8`, and positive since the fields are real, hence both equal `8`; the
discriminant being a complete invariant, the two fields are isomorphic, hence equal since they are
normal. This is the pigeonhole used in `prop_kw_2_power_real`. -/
theorem prop_kw_2_quadratic_real_unique {A : Type*} [Field A] [CharZero A]
    (K₁ : IntermediateField ℚ A) [NumberField K₁] [IsTotallyReal K₁]
    (hK₁ : Module.finrank ℚ K₁ = 2) (hKram₁ : UnramifiedOutside K₁ 2)
    (K₂ : IntermediateField ℚ A) [NumberField K₂] [IsGalois ℚ K₂] [IsTotallyReal K₂]
    (hK₂ : Module.finrank ℚ K₂ = 2) (hKram₂ : UnramifiedOutside K₂ 2) :
    K₁ = K₂ := by
  have : discr K₁ = discr K₂ := by
    have : 0 < discr K₁ := discr_pos K₁ hK₁
    have : 0 < discr K₂ := discr_pos K₂ hK₂
    rw [((kw_2_quadratic_discr K₁ hK₁ hKram₁).resolve_left (by grind)).resolve_left (by grind),
      ((kw_2_quadratic_discr K₂ hK₂ hKram₂).resolve_left (by grind)).resolve_left (by grind)]
  let e := ((nonempty_algEquiv_iff_discr_eq K₁ K₂ hK₁ hK₂).mpr this).some
  refine eq_of_le_of_finrank_eq ?_ (by rw [hK₁, hK₂])
  intro x hx
  rw [← AlgHom.fieldRange_of_normal (K₁.val.comp e.symm.toAlgHom)]
  exact ⟨e ⟨x, hx⟩, by simp⟩

section MaximalReal

open IntermediateField IsCyclotomicExtension NumberField

variable {A : Type*} [Field A] [CharZero A] (L : IntermediateField ℚ A) [NumberField L]
  [IsCMField L]

/-- The maximal real subfield `L⁺` of a CM field `L ⊆ A`, as an intermediate field of `A / ℚ`. -/
noncomputable def maximalReal : IntermediateField ℚ A :=
  lift ((NumberField.maximalRealSubfield L).toIntermediateField fun x ↦ by
    simp)

omit [NumberField L] [IsCMField L] in
theorem maximalReal_le : maximalReal L ≤ L := lift_le _

/-- The maximal real subfield of `L`, lifted to an intermediate field of `A / ℚ`, is isomorphic
to `L⁺`. -/
noncomputable def maximalRealAlgEquiv : maximalRealSubfield L ≃ₐ[ℚ] maximalReal L :=
  (liftAlgEquiv ((maximalRealSubfield L).toIntermediateField fun x ↦ by simp))

instance isTotallyReal_maximalReal : IsTotallyReal (maximalReal L) :=
  IsTotallyReal.ofRingEquiv (maximalRealAlgEquiv L).toRingEquiv

/-- `⟨c⟩` has order `2`, so its index is half the degree of `L`. -/
theorem index_zpowers_ratComplexConj [IsGalois ℚ L] :
    (Subgroup.zpowers (IsCMField.ratComplexConj L)).index * 2 = Module.finrank ℚ L := by
  rw [← IsCMField.orderOf_ratComplexConj L, ← Nat.card_zpowers, Subgroup.index_mul_card,
    IsGalois.card_aut_eq_finrank]

/-- `L⁺` is the fixed field of complex conjugation. -/
theorem maximalReal_eq_lift_fixedField :
    maximalReal L = lift (fixedField (Subgroup.zpowers (IsCMField.ratComplexConj L))) := by
  classical
  rw [maximalReal]
  congr
  ext x
  simp only [mem_fixedField_iff, mem_zpowers_iff_mem_range_orderOf,
    IsCMField.orderOf_ratComplexConj, Finset.mem_image, Finset.mem_range, Order.lt_two_iff,
    Nat.le_one_iff_eq_zero_or_eq_one, exists_eq_or_imp, pow_zero, existsAndEq, pow_one, true_and,
    or_imp, forall_and, forall_eq', AlgEquiv.one_apply, IsCMField.ratComplexConj_apply,
    IsCMField.complexConj_eq_self_iff]
  rfl

end MaximalReal

open IntermediateField in
/-- **Real case.** A totally real cyclic extension of `ℚ` of degree `2^m` unramified outside `2` is
contained in `ℚ(ζ_{2^{m+2}}) = ℚ⟮ξ (2^(m+2))⟯`.

Plan: let `K' := ℚ(ζ_{2^{m+2}})⁺` (the maximal real subfield, cyclic of degree `2^m`, unramified
outside `2`). If `K ⊔ K'` were not cyclic, its Galois group (a non-cyclic finite abelian `2`-group)
would have two distinct index-`2` subgroups
(`IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic`), giving two distinct quadratic subfields —
both totally real (`K ⊔ K'` is totally real) and unramified outside `2` — contradicting
`prop_kw_2_quadratic_real_unique`. So `K ⊔ K'` is cyclic, and `kw_cyclic_compositum` gives
`K ≤ K' ≤ ℚ⟮ξ (2^(m+2))⟯`. -/
theorem prop_kw_2_power_real {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    [IsTotallyReal K] (hK : Module.finrank ℚ K = 2 ^ m) (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ (2 ^ (m + 2))⟯ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAbelianGalois ℚ K := IsAbelianGalois.of_isCyclic ℚ K
  have hCcyc : IsCyclotomicExtension {2 ^ (m + 2)} ℚ ℚ⟮ξ (2 ^ (m + 2))⟯ :=
    (hξ (2 ^ (m + 2))).adjoinSimple_isCyclotomicExtension (2 ^ (m + 2)) ℚ A
  have : NumberField ℚ⟮ξ (2 ^ (m + 2))⟯ := IsCyclotomicExtension.numberField {2 ^ (m + 2)} ℚ _
  -- `K' = ℚ(ζ_{2^{m+2}})⁺`, the maximal real subfield: cyclic of degree `2^m`, totally real,
  -- unramified outside `2`, contained in `ℚ(ζ_{2^{m+2}})`.
  have : IsAbelianGalois ℚ ℚ⟮ξ (2 ^ (m + 2))⟯ :=
    IsCyclotomicExtension.isAbelianGalois {2 ^ (m + 2)} ℚ _
  have : IsCMField ℚ⟮ξ (2 ^ (m + 2))⟯ :=
    IsCyclotomicExtension.Rat.isCMField _ (S := {2 ^ (m + 2)})
      ⟨2 ^ (m + 2), rfl, by
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by lia)⟩
  -- `ℚ(ζ_{2^{m+2}})` is unramified outside `2`
  have hCram : UnramifiedOutside ℚ⟮ξ (2 ^ (m + 2))⟯ 2 := by
    intro q hq hq2
    have : Fact (q.Prime) := ⟨hq⟩
    apply isUnramifiedIn_of_isCyclotomicExtension (p := q) (n := 2 ^ (m + 2))
    intro h
    exact hq2 <| Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  obtain ⟨K', hK'le, hK'deg, hK'gal, hK'cyc, hK'ram, hK'real⟩ :
      ∃ K' : IntermediateField ℚ A, K' ≤ ℚ⟮ξ (2 ^ (m + 2))⟯ ∧ Module.finrank ℚ K' = 2 ^ m ∧
        IsGalois ℚ K' ∧ IsCyclic Gal(K'/ℚ) ∧ UnramifiedOutside K' 2 ∧ IsTotallyReal K' := by
    -- `K'` is the maximal real subfield, i.e. the fixed field of complex conjugation
    obtain ⟨hdeg, hgal, hcyc, hram⟩ :=
      fixedField_spec_of_index_eq_prime_pow (p := 2) (m := m) ℚ⟮ξ (2 ^ (m + 2))⟯ hCram
        (Subgroup.zpowers (IsCMField.ratComplexConj ℚ⟮ξ (2 ^ (m + 2))⟯))
        (by -- index `2 ^ m`: half of `[ℚ(ζ_{2^{m+2}}) : ℚ] = 2 ^ (m + 1)`
          rw [Subgroup.index_eq_card_div, Nat.card_zpowers, IsCMField.orderOf_ratComplexConj,
            IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank (2 ^ (m + 2)),
            Nat.totient_prime_pow Nat.prime_two (by norm_num), Nat.add_one_sub_one,
            Nat.add_one_sub_one, mul_one, Nat.pow_succ, Nat.mul_div_cancel _ zero_lt_two])
        (by
          rw [MulEquiv.isCyclic (QuotientGroup.congr _ _
            (IsCyclotomicExtension.Rat.galEquivZMod (2 ^ (m + 2)) _) rfl)]
          rw [MonoidHom.map_zpowers, MonoidHom.coe_ofClass]
          rw [IsCyclotomicExtension.Rat.galEquivZMod_ratComplexConj]
          exact ZMod.isCyclic_units_two_pow_quotient_neg_one m)
    rw [← maximalReal_eq_lift_fixedField] at hdeg hgal hcyc hram
    exact ⟨maximalReal ℚ⟮ξ (2 ^ (m + 2))⟯, maximalReal_le _, hdeg, hgal, hcyc, hram,
      isTotallyReal_maximalReal _⟩
  have : NumberField K' :=
    let : Algebra K' ℚ⟮ξ (2 ^ (m + 2))⟯ := (inclusion hK'le).toAlgebra
    NumberField.of_tower ℚ ℚ⟮ξ (2 ^ (m + 2))⟯ _
  have : IsGalois ℚ K' := hK'gal
  have : IsCyclic Gal(K'/ℚ) := hK'cyc
  have : IsTotallyReal K' := hK'real
  have : IsAbelianGalois ℚ K' := IsAbelianGalois.of_isCyclic ℚ K'
  -- The compositum `K ⊔ K'` is totally real (both factors are).
  have hsupreal : IsTotallyReal ↑(K ⊔ K') := by
    change IsTotallyReal ↑(K ⊔ K').toSubfield
    rw [sup_toSubfield]
    apply NumberField.isTotallyReal_sup'
  refine (kw_eq_of_unique_prime_subfield K K' hK hK'deg hKram hK'ram ?_).le.trans hK'le
  intro F₁ F₂ _ _ _ _ _ _ hle₁ hle₂ hf₁ hf₂ hr₁ hr₂
  let : Algebra F₁ ↑(K ⊔ K') := (inclusion hle₁).toAlgebra
  let : Algebra F₂ ↑(K ⊔ K') := (inclusion hle₂).toAlgebra
  have : IsScalarTower ℚ F₁ ↑(K ⊔ K') :=
    IsScalarTower.of_algebraMap_eq fun x => ((inclusion hle₁).commutes x).symm
  have : IsScalarTower ℚ F₂ ↑(K ⊔ K') :=
    IsScalarTower.of_algebraMap_eq fun x => ((inclusion hle₂).commutes x).symm
  have : IsTotallyReal F₁ := IsTotallyReal.of_algebra F₁ ↑(K ⊔ K')
  have : IsTotallyReal F₂ := IsTotallyReal.of_algebra F₂ ↑(K ⊔ K')
  exact prop_kw_2_quadratic_real_unique F₁ hf₁ hr₁ F₂ hf₂ hr₂

set_option maxHeartbeats 400000 in
-- reason for change
open IntermediateField in
/-- Every cyclic extension of `ℚ` of degree `2ᵐ` unramified outside `2` is cyclotomic: contained in
`ℚ(ζ_{2^{m+2}}) = ℚ⟮ξ (2^(m+2))⟯` inside the ambient field `A`.

Plan (reduce the general case to `prop_kw_2_power_real`): if `K` is totally real, apply the real
case directly. Otherwise pass to `K(i) = K · ℚ(i)`, a CM field with maximal real subfield `M`
(`K(i) = M(i)`); `M` is real, cyclic, of `2`-power degree, and unramified outside `2`, so the real
case makes `M` — and hence `K` — cyclotomic. -/
theorem prop_kw_2_power {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (hK : Module.finrank ℚ K = 2 ^ m) (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ (2 ^ (m + 2))⟯ := by
  -- if `K` is already totally real, the real case applies directly
  by_cases hreal : IsTotallyReal K
  · exact prop_kw_2_power_real hξ m K hK hKram
  -- otherwise pass to `L = K(i) = K ⊔ ℚ(i)`, which is CM
  have : IsCyclotomicExtension {2 ^ (m + 2)} ℚ ℚ⟮ξ (2 ^ (m + 2))⟯ :=
    (hξ (2 ^ (m + 2))).adjoinSimple_isCyclotomicExtension (2 ^ (m + 2)) ℚ A
  have : IsCyclotomicExtension {4} ℚ ℚ ⟮ξ 4⟯ := (hξ 4).adjoinSimple_isCyclotomicExtension 4 ℚ A
  have : NumberField ℚ⟮ξ 4⟯ := IsCyclotomicExtension.numberField {4} ℚ _
  have : IsAbelianGalois ℚ ℚ⟮ξ 4⟯ := IsCyclotomicExtension.isAbelianGalois {4} ℚ ℚ⟮ξ 4⟯
  have : IsTotallyComplex ℚ⟮ξ 4⟯ :=
    IsCyclotomicExtension.Rat.isTotallyComplex ℚ⟮ξ 4⟯ (by norm_num : 3 ≤ 4)
  have : IsAbelianGalois ℚ K := IsAbelianGalois.of_isCyclic _ _
  set L : IntermediateField ℚ A := K ⊔ ℚ⟮ξ 4⟯ with hL
  have hKL : K ≤ L := le_sup_left
  have : IsTotallyComplex L := by
    have : Algebra ℚ⟮ξ 4⟯ L := RingHom.toAlgebra (inclusion le_sup_right).toRingHom
    exact isTotallyComplex_of_algebra ℚ⟮ξ 4⟯ L
  have hLram : UnramifiedOutside L 2 :=
    unramifiedOutside_sup 2 K ℚ⟮ξ 4⟯ hKram fun q hq hq2 ↦
      have : Fact q.Prime := ⟨hq⟩
      isUnramifiedIn_of_isCyclotomicExtension (n := 4) q
        fun h ↦ hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
          (hq.dvd_of_dvd_pow (n := 2) (by norm_num at h ⊢; exact h)))
  -- its maximal real subfield `M` is cyclic of `2`-power degree, unramified outside `2`
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l, l ≤ m + 1 ∧ Module.finrank ℚ L = 2 ^ l := by
    rw [← Nat.dvd_prime_pow Nat.prime_two]
    convert finrank_sup_dvd_mul_of_isGalois K ℚ⟮ξ 4⟯
    rw [hK, IsCyclotomicExtension.Rat.finrank 4, show 4 = 2 ^ 2 by rfl, Nat.totient_prime_pow
      Nat.prime_two (by positivity), Nat.add_one_sub_one, pow_one, mul_one, Nat.pow_succ]
  set M : IntermediateField ℚ A := maximalReal L with hM
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k, k ≤ l ∧ Module.finrank ℚ M = 2 ^ k := by
    rw [← Nat.dvd_prime_pow Nat.prime_two, ← hl₂]
    exact finrank_dvd_of_le_right <| maximalReal_le L
  have : NumberField M := by
    refine
      { to_charZero := charZero M, to_finiteDimensional := FiniteDimensional.of_finrank_pos ?_ }
    rw [hk₂]
    exact Nat.two_pow_pos k
  have hML : M ≠ L := fun h ↦ by
    have : IsTotallyReal L := h ▸ isTotallyReal_maximalReal L
    obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
    exact IsTotallyComplex.complexEmbedding_not_isReal φ <| IsTotallyReal.complexEmbedding_isReal φ
  have hkm : k ≤ m := by
    refine (Nat.le_add_one_iff.mp <| hk₁.trans hl₁).resolve_right fun h ↦ hML ?_
    apply IntermediateField.eq_of_le_of_finrank_le (maximalReal_le L)
    rwa [hl₂, hk₂, Nat.pow_le_pow_iff_right one_lt_two, h]
  have hMram : UnramifiedOutside M 2 := by
    have : Algebra M L := (inclusion (maximalReal_le L)).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot _ hLram
  have : IsAbelianGalois ℚ M := by
    have : Algebra M L := (inclusion (maximalReal_le L)).toRingHom.toAlgebra
    exact IsAbelianGalois.tower_bot ℚ _ L
  have : IsCyclic ((Gal(K/ℚ) × Gal(ℚ⟮ξ 4⟯/ℚ)) ⧸
      Subgroup.map (K.restrictNormalHomSupProd ℚ⟮ξ 4⟯)
        (Subgroup.zpowers (IsCMField.ratComplexConj L))) := by
    apply isCyclic_quotient_of_sup_range_eq_top _ (MonoidHom.inl _ _)
    rw [MonoidHom.range_inl, sup_comm, ← Subgroup.comap_map_eq, Subgroup.map_map]
    rw [MonoidHom.map_zpowers, MonoidHom.coe_comp, Function.comp_apply]
    rw [restrictNormalHomSupProd_apply, MonoidHom.coe_snd]
    dsimp only
    let : Algebra ℚ⟮ξ 4⟯ L := (inclusion le_sup_right).toRingHom.toAlgebra
    rw [IsCMField.restrictNormalHom_ratComplexConj]
    rw [Subgroup.eq_top_of_card_eq (Subgroup.zpowers _)]
    · rw [Subgroup.comap_top]
    rw [Nat.card_zpowers]
    rw [IsCMField.orderOf_ratComplexConj]
    rw [IsGalois.card_aut_eq_finrank]
    rw [IsCyclotomicExtension.Rat.finrank 4]
    decide
  have : IsCyclic Gal(M/ℚ) := by
    suffices IsCyclic (Gal(L/ℚ) ⧸ Subgroup.zpowers (IsCMField.ratComplexConj L)) by
      let M₀ := maximalRealSubfield L
      exact (AlgEquiv.autCongr (maximalRealAlgEquiv L)).isCyclic.mp
        <| (IsGaloisGroup.mulEquivCongr _ Gal(M₀/ℚ) ℚ M₀).isCyclic.mp this
    refine isCyclic_of_injective
      (QuotientGroup.map (Subgroup.zpowers (IsCMField.ratComplexConj L)) _
        (restrictNormalHomSupProd K ℚ⟮ξ 4⟯) (Subgroup.le_comap_map _ _)) ?_
    rw [QuotientGroup.injective_map_iff]
    rw [Subgroup.comap_map_eq, MonoidHom.ker_eq_bot, sup_bot_eq]
    exact restrictNormalHomSupProd_injective K ℚ⟮ξ 4⟯
    -- `M = L⁺`, so `Gal(M/ℚ) ≅ Gal(L/ℚ) ⧸ ⟨c⟩`, which embeds in
    -- `(Gal(K/ℚ) × Gal(ℚ(i)/ℚ)) ⧸ ⟨e c⟩` since `e` is injective. That quotient is generated by
    -- the image of `Gal(K/ℚ)`, because `c` restricted to `ℚ(i)` is non-trivial, so it is cyclic,
    -- and a subgroup of a cyclic group is cyclic
  -- the real case applies to `M`
  have hM' : M ≤ ℚ⟮ξ (2 ^ (k + 2))⟯ := prop_kw_2_power_real hξ k M hk₂ hMram
  -- and `K ≤ L = M(i) ≤ ℚ(ζ_{2^{k+2}}) ⊔ ℚ(i) ≤ ℚ(ζ_{2^{m+2}})`
  have hLM : M ⊔ ℚ⟮ξ 4⟯ = L := by
    -- `M ⊔ ℚ⟮ξ 4⟯ ≤ L` by `sup_le`, and `M ≤ M ⊔ ℚ⟮ξ 4⟯`. Now `M = L⁺` is the fixed field of
    -- `⟨c⟩`, which has order `2`, so `[L : M] = 2` and nothing lies strictly between `M` and `L`.
    -- Since `M` is totally real, `ξ 4 ∉ M`, hence `M ⊔ ℚ⟮ξ 4⟯ ≠ M` and so `M ⊔ ℚ⟮ξ 4⟯ = L`.
    refine eq_of_le_of_finrank_le (sup_le (maximalReal_le L) le_sup_right) ?_
    obtain ⟨c, hc⟩ := finrank_dvd_of_le_right (le_sup_left : M ≤ M ⊔ ℚ⟮ξ 4⟯)
    rw [hc]
    rw [IsCMField.finrank_eq_two_mul, mul_comm]
    gcongr
    · exact le_of_eq <| LinearEquiv.finrank_eq (maximalRealAlgEquiv L).toLinearEquiv
    · by_contra! h
      interval_cases c
      · rw [mul_zero] at hc
        exact Module.finrank_pos.ne hc.symm
      · have := eq_of_le_of_finrank_eq (le_sup_left : M ≤ M ⊔ ℚ⟮ξ 4⟯)
          (by rwa [mul_one, eq_comm] at hc)
        have : IsTotallyComplex M := by
          rw [this]
          let : Algebra ℚ⟮ξ 4⟯ ↑(M ⊔ ℚ⟮ξ 4⟯) := (inclusion le_sup_right).toRingHom.toAlgebra
          apply isTotallyComplex_of_algebra ℚ⟮ξ 4⟯
        obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
        exact IsTotallyComplex.complexEmbedding_not_isReal φ <|
          IsTotallyReal.complexEmbedding_isReal φ
  -- Module.finrank_dvd_finrank_right ℚ M ↑(M ⊔ ℚ⟮ξ 4⟯)
  -- K ≤ L = M ⊔ ℚ⟮ξ 4⟯ ≤ ℚ⟮ξ (2^(k+2))⟯ ⊔ ℚ⟮ξ 4⟯ ≤ ℚ⟮ξ (2^(m+2))⟯
  refine hKL.trans ?_
  have := sup_le_sup_right hM' ℚ⟮ξ 4⟯
  rw [← hLM]
  refine le_trans this ?_
  apply sup_le
  · have : IsCyclotomicExtension {2 ^ (k + 2)} ℚ ℚ⟮ξ (2 ^ (k + 2))⟯ :=
      (hξ (2 ^ (k + 2))).adjoinSimple_isCyclotomicExtension (2 ^ (k + 2)) ℚ A
    apply isCyclotomicExtension_le_of_dvd _ _ (2 ^ (k + 2)) (2 ^ (m + 2))
    apply Nat.pow_dvd_pow
    lia
  · apply isCyclotomicExtension_le_of_dvd _ _ 4 (2 ^ (m + 2))
    lia

end

end
