module

public import Mathlib.NumberTheory.JacobiSum.Basic

public import SKW.Stickelberger.AddCharTrace
public import SKW.Stickelberger.Misc

set_option linter.style.header false

/-!
# Gauss sums

This file holds the Gauss sums attached to the Teichmüller character, with the properties of them
that `SKW.Stickelberger.{Factorization, valGauss, Stickelberger}` rely on. The statements carry no
proof for the moment; the earlier proofs are kept in `SKW.Stickelberger.rGaussSum`, which is not
part of the build. The auxiliary results that have nothing to do with Gauss sums live in
`SKW.Stickelberger.Misc`.
-/

@[expose] public section

noncomputable section

namespace Stickelberger

open Ideal NumberField IntermediateField

variable {p : ℕ} (n : ℕ)

local notation3 "𝒑" => span {(p : ℤ)}

variable {L : Type*} [Field L] [NumberField L] {K F : IntermediateField ℚ L}

variable (P : Ideal (𝓞 K)) (𝓟 : Ideal (𝓞 L)) [P.HasTeichmullerLift n]

variable {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p)

attribute [local instance] ZMod.algebra

attribute [local instance] Ideal.Quotient.field

theorem cast_trace_eq_algebraMap_trace [P.LiesOver 𝒑] [CharP (𝓞 K ⧸ P) p]
    [Algebra (ℤ ⧸ 𝒑) (𝓞 L ⧸ 𝓟 ^ 2)] (x : 𝓞 K ⧸ P) :
    (Algebra.trace (ZMod p) (𝓞 K ⧸ P) x).cast =
      algebraMap _ (𝓞 L ⧸ 𝓟 ^ 2) (Algebra.trace (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) x) := by
  rw [← ZMod.cast_trace_eq_trace (Int.quotientSpanNatEquivZMod p), ZMod.map_cast]

@[nolint defsWithUnderscore]
local instance [NeZero P] : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

section Teichmuller

variable [NeZero n] [IsCyclotomicExtension {n} ℚ K]

protected theorem teichmuller_ne_one (hn : n ≠ 1) :
    MulChar.teichmuller P n ≠ 1 :=
  MulChar.teichmuller_ne_one (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot hn

theorem teichmuller_ringHomComp_zpow_ne_one {a : ℤ}
    (ha : ¬ (n : ℤ) ∣ a) :
    (MulChar.teichmuller P n ^ a).ringHomComp (algebraMap (𝓞 K) (𝓞 L)) ≠ 1 := by
  rw [MulChar.ringHomComp_ne_one_iff]
  · rwa [ne_eq, MulChar.teichmuller_zpow_eq_one_iff] --  Int.dvd_neg]
    exact (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  · exact RingOfIntegers.algebraMap.injective K L

end Teichmuller

/-- Docstring. -/
protected def gaussSum [NeZero p] [P.LiesOver 𝒑] (a : ℤ) : 𝓞 L :=
  haveI : NeZero P := ⟨Ideal.ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using NeZero.ne p) _⟩
  haveI : CharP (𝓞 K ⧸ P) p := ringChar.of_eq ringChar_quotient_eq
  gaussSum (((MulChar.teichmuller P n) ^ (- a)).ringHomComp (algebraMap (𝓞 K) (𝓞 L)))
    ((algebraMap (𝓞 F) (𝓞 L)).compAddChar (AddChar.traceChar (𝓞 K ⧸ P) hζ))

local notation3 "𝓖" => Stickelberger.gaussSum

protected def jacobiSum [P.IsMaximal] (a b : ℤ) : 𝓞 K :=
  jacobiSum (MulChar.teichmuller P n ^ (-a)) (MulChar.teichmuller P n ^ (-b))

local notation3 "𝓙" => Stickelberger.jacobiSum

section

-- The notation `𝒑` cannot be used in a `variable` command, since it refers to the variable `p`.
variable [NeZero p] [P.LiesOver (span {(p : ℤ)})]

theorem gaussSum_def (a : ℤ) :
    haveI : NeZero P := ⟨Ideal.ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using NeZero.ne p) _⟩
    haveI : CharP (𝓞 K ⧸ P) p := ringChar.of_eq ringChar_quotient_eq
    𝓖 n P hζ a =
      gaussSum (((MulChar.teichmuller P n) ^ (- a)).ringHomComp (algebraMap (𝓞 K) (𝓞 L)))
      ((algebraMap (𝓞 F) (𝓞 L)).compAddChar (AddChar.traceChar (𝓞 K ⧸ P) hζ)) := rfl

theorem gaussSum_periodic {k : ℤ} (hk : (n : ℤ) ∣ k) (a : ℤ) :
    𝓖 n P hζ (a + k) = 𝓖 n P hζ a := by
  rw [gaussSum_def, gaussSum_def, neg_add, zpow_add,
    MulChar.teichmuller_zpow_eq_one_of_dvd (Int.dvd_neg.mpr hk), mul_one]

section

variable [NeZero n] [IsCyclotomicExtension {n} ℚ K]

theorem gaussSum_mem_span_zeta_sub_one (a : ℤ) (ha : ¬ (n : ℤ) ∣ a) :
    𝓖 n P hζ a ∈ Ideal.span {algebraMap (𝓞 F) (𝓞 L) ζ - 1} := by
  have : NeZero P := ⟨Ideal.ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using NeZero.ne p) _⟩
  simp_rw [gaussSum_def, gaussSum, AddChar.compAddChar_traceChar_algebraMap,
    ← Quotient.eq_zero_iff_mem, map_sum, map_mul,
    AddChar.mk_traceChar_apply_eq_one _ (mem_span_singleton_self _), mul_one, ← map_sum]
  rw [MulChar.sum_eq_zero_of_ne_one (teichmuller_ringHomComp_zpow_ne_one n P
    (by rwa [Int.dvd_neg])), map_zero]

theorem gaussSum_mul_gaussSum [P.IsMaximal] (a b : ℤ) (h : ¬ (n : ℤ) ∣ a + b) :
    𝓖 n P hζ a * 𝓖 n P hζ b =
      𝓖 n P hζ (a + b) * algebraMap (𝓞 K) (𝓞 L) (𝓙 n P a b) := by
  rw [gaussSum_def, gaussSum_def, gaussSum_def, ← jacobiSum_mul_nontrivial,
    ← MulChar.ringHomComp_mul, ← zpow_add, neg_add, jacobiSum_ringHomComp,
    Stickelberger.jacobiSum]
  rw [← MulChar.ringHomComp_mul, ← zpow_add, ← neg_add]
  exact teichmuller_ringHomComp_zpow_ne_one n P (by rwa [Int.dvd_neg])

end

end

section

variable [Fact p.Prime] [P.IsMaximal] [P.LiesOver (span {(p : ℤ)})]

theorem gaussSum_zero :
    𝓖 n P hζ 0 = -1 := by
  have : CharP (𝓞 K ⧸ P) p := ringChar.of_eq ringChar_quotient_eq
  rw [gaussSum_def, neg_zero, zpow_zero, MulChar.ringHomComp_one, gaussSum_one_left]
  rw [AddChar.compAddChar_traceChar_algebraMap]
  exact AddChar.traceChar_ne_one _

theorem gaussSum_of_dvd (a : ℤ) (ha : (n : ℤ) ∣ a) :
    𝓖 n P hζ a = -1 := by
  rwa [← zero_add a, gaussSum_periodic, gaussSum_zero]

theorem gaussSum_frob (a : ℤ) :
    𝓖 n P hζ (p * a) = 𝓖 n P hζ a := by
  have : CharP (𝓞 K ⧸ P) p := ringChar.of_eq ringChar_quotient_eq
  have : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite _
  rw [gaussSum_def, gaussSum_def, gaussSum, gaussSum, eq_comm,
    ← ((FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) _ p).bijective).sum_comp]
  refine Fintype.sum_congr _ _ fun _ ↦ ?_
  rw [FiniteField.frobeniusAlgEquiv_apply, Fintype.card_eq_nat_card, Int.card_ideal_quot,
    MonoidHom.coe_compAddChar, Function.comp_apply, Function.comp_apply,
    AddChar.traceChar_apply_pow, map_pow, ← MulChar.pow_apply' _ (Fact.out : p.Prime).ne_zero,
    MulChar.ringHomComp_pow, ← zpow_natCast, ← zpow_mul, neg_mul, mul_comm a]

section

variable [NeZero n] [IsCyclotomicExtension {n} ℚ K]

theorem gaussSum_mul_gaussSum_neg (a : ℤ) (ha : ¬ (n : ℤ) ∣ a) :
    𝓖 n P hζ a * 𝓖 n P hζ (-a) =
      algebraMap (𝓞 K) (𝓞 L) (((MulChar.teichmuller P n) ^ (- a)) (- 1)) * p ^ P.inertiaDeg ℤ := by
  have : CharP (𝓞 K ⧸ P) p := ringChar.of_eq ringChar_quotient_eq
  rw [gaussSum_def, gaussSum_def, ← mul_gaussSum_inv_eq_gaussSum,
    AddChar.compAddChar_traceChar_algebraMap, neg_neg, zpow_neg, ← MulChar.ringHomComp_inv,
    mul_right_comm, mul_assoc, gaussSum_mul_gaussSum_eq_card, Fintype.card_eq_nat_card,
    ← absNorm_eq_card, ← Ideal.pow_inertiaDeg p P, Nat.cast_pow, MulChar.ringHomComp_inv,
    MulChar.ringHomComp_apply]
  · exact teichmuller_ringHomComp_zpow_ne_one n P ha
  · apply AddChar.isPrimitive_traceChar _

omit [P.IsMaximal] in
theorem not_isUnit_gaussSum (a : ℤ) (ha : ¬ (n : ℤ) ∣ a) :
    ¬ IsUnit (𝓖 n P hζ a) := by
  have hp : p.Prime := Fact.out
  have h : span {(algebraMap (𝓞 F) (𝓞 L)) (ζ - 1)} ≠ ⊤ := by
    rw [ne_eq, span_singleton_eq_top, isUnit_map_iff, hζ.isUnit_sub_one_iff hp.one_lt, not_not]
    exact ⟨p, 1, hp.prime, zero_lt_one, by rw [pow_one]⟩
  contrapose! h
  rw [map_sub, map_one]
  exact Ideal.eq_top_of_isUnit_mem _ (gaussSum_mem_span_zeta_sub_one n P hζ a ha) h

theorem norm_gaussSum (a : ℤ) (ha : ¬ (n : ℤ) ∣ a) :
    ∃ k, 1 ≤ k ∧ (Algebra.norm ℤ (𝓖 n P hζ a)).natAbs = p ^ k := by
  have h := congr_arg (Int.natAbs <| Algebra.norm ℤ ·) <| gaussSum_mul_gaussSum_neg n P hζ _ ha
  rw [map_mul, map_mul, Int.natAbs_mul, Int.natAbs_mul, zpow_neg,
    ← map_natCast (algebraMap ℤ (𝓞 L)), map_pow,
    Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis L), ← pow_mul,
    isUnit_iff_natAbs_norm.mp (RingHom.isUnit_map (algebraMap (𝓞 K) (𝓞 L)) _), one_mul,
    Int.natAbs_pow, Int.natAbs_natCast] at h
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp (Dvd.intro _ h)
    refine ⟨k, ?_, hk⟩
    by_contra! h
    refine not_isUnit_gaussSum n P hζ a ha ?_
    rw [isUnit_iff_natAbs_norm, hk,  Nat.lt_one_iff.mp h, pow_zero]
  · rw [MulChar.inv_apply', inv_neg, inv_one]
    exact isUnit_neg_one.map _

end

end

section IsCycloF

variable [Fact p.Prime] [NumberField F] [IsCyclotomicExtension {p} ℚ F]
    [P.LiesOver (span {(p : ℤ)})]

theorem gaussSum_mem [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    [𝓟.IsPrime] [𝓟.LiesOver 𝒑] (a : ℤ) (ha : ¬ (n : ℤ) ∣ a) :
    𝓖 n P hζ a ∈ 𝓟 :=
  (span_singleton_le_iff_mem 𝓟).mpr (zeta_sub_one_mem hζ 𝓟) <|
    gaussSum_mem_span_zeta_sub_one n P hζ a ha

variable [P.IsMaximal]

omit [P.HasTeichmullerLift n] in
private theorem sum_teichmuller_inv_mul_cast_trace_aux (i : ℕ) :
    ∑ a : 𝓞 K ⧸ P, a⁻¹ * a ^ p ^ i = if P.inertiaDeg ℤ ∣ i then -1 else 0  := by
  rw [← Nat.succ_pred_eq_of_pos (NeZero.pos (p ^ i)), FiniteField.sum_inv_mul_pow_succ]
  obtain rfl | hi := Nat.eq_zero_or_pos i
  · simp
  · rw [Fintype.card_eq_nat_card, ← absNorm_eq_card, ← Ideal.pow_inertiaDeg p P,
      Nat.pred_eq_sub_one,
      if_congr (Nat.pow_sub_one_dvd_pow_sub_one_iff (Fact.out : p.Prime).one_lt) rfl rfl]

private theorem sum_teichmuller_inv_mul_cast_trace [CharP (𝓞 K ⧸ P) p] [(𝓟 ^ 2).LiesOver P] :
    ∑ x : 𝓞 K ⧸ P, algebraMap (𝓞 K) (𝓞 L ⧸ 𝓟 ^ 2) ((MulChar.teichmuller P n)⁻¹ x) *
      (Algebra.trace (ZMod p) (𝓞 K ⧸ P) x).cast = - 1 := by
  classical
  have : (𝓟 ^ 2).LiesOver 𝒑 := LiesOver.trans (𝓟 ^ 2) P 𝒑
  simp_rw [cast_trace_eq_algebraMap_trace,
    IsScalarTower.algebraMap_apply (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2),
    FiniteField.algebraMap_trace_eq_sum_pow (ℤ ⧸ 𝒑) (𝓞 K ⧸ P), map_sum, Finset.mul_sum,
    IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K ⧸ P) (𝓞 L ⧸ 𝓟 ^ 2), MulChar.inv_apply',
    Quotient.algebraMap_eq, MulChar.mk_teichmuller_apply]
  rw [Finset.sum_comm]
  simp_rw [← map_mul, ← map_sum, Int.card_ideal_quot, sum_teichmuller_inv_mul_cast_trace_aux]
  rw [inertiaDeg_eq_of_isMaximal 𝒑 P, ← Nat.succ_pred_eq_of_pos (n := Module.finrank _ _)
    Module.finrank_pos, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add,
    ite_eq_left (Nat.dvd_zero _), map_neg, map_one]
  intro _ _
  rw [ite_eq_right]
  exact (Nat.le_of_dvd (Nat.succ_pos _)).mt (by grind)

theorem mk_sq_gaussSum_eq [hp' : Fact (Odd p)] [IsCyclotomicExtension {n} ℚ K]
    [𝓟.IsPrime] [𝓟.LiesOver P] (hn : 1 < n) (h𝓟 : 2 ≤ 𝓟.ramificationIdx (𝓞 K)) :
    Ideal.Quotient.mk (𝓟 ^ 2) (𝓖 n P hζ 1) = -(algebraMap (𝓞 F) (𝓞 L) ζ - 1 :) := by
  classical
  have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have : NeZero P := ⟨Ideal.ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using NeZero.ne p) _⟩
  have : CharP (𝓞 K ⧸ P) p := ringChar.of_eq ringChar_quotient_eq
  have h3 : 3 ≤ p := (Nat.Prime.odd_iff Fact.out).mp hp'.out
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have : (𝓟 ^ 2).LiesOver P := by
    refine pow_liesOver_of_liesOver P 𝓟 ?_
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (NeZero.ne P)]
    exact h𝓟
  have : (𝓟 ^ 2).LiesOver 𝒑 := LiesOver.trans (𝓟 ^ 2) P 𝒑
  have hζ₀ := hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))
  have h𝓟 := zeta_sub_one_mem hζ 𝓟
  have h : (MulChar.teichmuller P n)⁻¹ ≠ 1 :=
    inv_ne_one.mpr <| MulChar.teichmuller_ne_one
      (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot hn.ne'
  rw [gaussSum_def, gaussSum]
  simp_rw [zpow_neg, zpow_one, MulChar.ringHomComp_apply, map_sum, map_mul,
    AddChar.compAddChar_traceChar_algebraMap,
    AddChar.mk_traceChar_apply_eq_one_add_smul hζ₀ h𝓟, mul_add, mul_one,
    Finset.sum_add_distrib, ← map_sum, MulChar.sum_eq_zero_of_ne_one h, map_zero, zero_add,
    Algebra.smul_def, ← mul_assoc, ← Finset.sum_mul, Quotient.mk_algebraMap, eq_natCast,
    ZMod.natCast_val, sum_teichmuller_inv_mul_cast_trace, map_neg, map_sub,
    Quotient.mk_algebraMap, map_one, neg_mul, one_mul]

end IsCycloF
section Galois

variable (p) [NeZero p] [NeZero n] [Fact (n.Coprime p)] [IsCyclotomicExtension {p * n} ℚ L]

theorem smul_traceChar [CharP (𝓞 K ⧸ P) p] (σ : Gal(L/F)) (x : 𝓞 K ⧸ P) :
    σ • (algebraMap (𝓞 F) (𝓞 L)).compAddChar (AddChar.traceChar (𝓞 K ⧸ P) hζ) x =
      (algebraMap (𝓞 F) (𝓞 L)).compAddChar (AddChar.traceChar (𝓞 K ⧸ P) hζ) x := by
  rw [AddChar.compAddChar_traceChar_algebraMap, smul_eq_galRestrict_apply (𝓞 F),
    AddChar.map_traceChar_apply_eq_mulShift _ _ 1, Nat.cast_one, AddChar.mulShift_one]
  rw [AlgEquiv.commutes, pow_one]

variable [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {n} ℚ K]

theorem galLFEquiv_apply_of_isPrimitiveRoot (σ : Gal(L/F)) {η : 𝓞 K} (hη : IsPrimitiveRoot η n) :
    σ • (algebraMap (𝓞 K) (𝓞 L) η) =
      (algebraMap (𝓞 K) (𝓞 L)) η ^ (galFEquiv p n K F σ).val.val := by
  have : Normal ℚ K := (IsCyclotomicExtension.isGalois {n} ℚ K).to_normal
  apply RingOfIntegers.coe_injective
  rw [algebraMap.smul', map_pow, ← IsScalarTower.algebraMap_apply, AlgEquiv.smul_def,
    IsScalarTower.algebraMap_apply (𝓞 K) K L, ← map_pow]
  have := RingHom.congr_arg (algebraMap K L) <|
     IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n K
      ((σ.restrictScalars ℚ).restrictNormalHom K) (x := (algebraMap (𝓞 K) K) η)
        (by rw [← map_pow, hη.pow_eq_one, map_one])
  rwa [IntermediateField.algebraMap_apply, AlgEquiv.restrictNormalHom_apply] at this

theorem smul_teichmuller (σ : Gal(L/F)) (a : ℤ) (x : 𝓞 K ⧸ P) :
    σ • (MulChar.teichmuller P n ^ (-a)).ringHomComp (algebraMap (𝓞 K) (𝓞 L)) x =
      (MulChar.teichmuller P n ^ (-(a * (galFEquiv p n K F σ).val.val))).ringHomComp
        (algebraMap (𝓞 K) (𝓞 L)) x := by
  let η : 𝓞 K := (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger
  have hη := (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  rw [smul_eq_galRestrict_apply (𝓞 F), MulChar.map_ringHomComp_teichmuller_zpow_apply _ _
    (galFEquiv p n K F σ).val.val hη, neg_mul]
  rw [← smul_eq_galRestrict_apply]
  exact galLFEquiv_apply_of_isPrimitiveRoot p n σ hη

theorem gal_gaussSum_eq_gaussSum [P.LiesOver 𝒑] (σ : Gal(L/F)) (a : ℤ) :
    σ • 𝓖 n P hζ a = 𝓖 n P hζ (a * (galFEquiv p n  K F σ).val.val) := by
  have : NeZero P := ⟨Ideal.ne_bot_of_liesOver_of_ne_bot (p := 𝒑) (by simpa using NeZero.ne p) _⟩
  rw [gaussSum_def, gaussSum_def, gaussSum, gaussSum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [smul_mul', smul_traceChar, smul_teichmuller p]

end Galois

end Stickelberger
