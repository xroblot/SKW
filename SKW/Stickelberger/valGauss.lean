module

public import Mathlib.Data.ENat.BigOperators

public import SKW.Stickelberger.GaussSum

@[expose] public section

noncomputable section

open Ideal NumberField IntermediateField Pointwise

variable (p f : ℕ) [NeZero (p ^ f - 1)]

local notation3 "𝒑" => span {(p : ℤ)}

variable {p f}

variable {L : Type*} [Field L] [NumberField L] {F K : IntermediateField ℚ L} {P : Ideal (𝓞 K)}

variable (hbij : Function.Bijective (rootsOfUnity.mapQuot (p ^ f - 1) P))

variable {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p) {η : 𝓞 K} (hη : IsPrimitiveRoot η (p ^ f - 1))

variable [P.IsMaximal] (𝓟 : Ideal (𝓞 L)) [hp : Fact (p.Prime)]

local instance : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite (𝓞 K ⧸ P)

attribute [local instance] Ideal.Quotient.field

abbrev valGauss [P.LiesOver 𝒑] (a : ℤ) : ℕ∞ := emultiplicity 𝓟 (span {(GaussSum hbij hζ a : 𝓞 L)})

omit [NeZero (p ^ f - 1)] in
theorem valGauss_frob [P.LiesOver 𝒑] (a : ℤ) :
    valGauss hbij hζ 𝓟 (p * a) = valGauss hbij hζ 𝓟 a := by
  rw [valGauss, valGauss, GaussSum_frob]

include hη

theorem valGauss_eq_zero [P.LiesOver 𝒑] [𝓟.IsPrime] (a : ℤ) (h : ↑(p ^ f - 1 : ℕ) ∣ a) :
    valGauss hbij hζ 𝓟 a = 0 := by
  rw [valGauss, GaussSum, orderOf_dvd_iff_zpow_eq_one.mp, MulChar.ringHomComp_one,
    gaussSum_one_left, span_singleton_neg, span_singleton_one, emultiplicity_bot]
  · exact IsPrime.ne_top'
  · rw [ne_eq, MonoidHom.compAddChar_eq_one_iff (FaithfulSMul.algebraMap_injective _ _)]
    exact addCharTrace_ne_one P hζ
  · rwa [orderOf_teichmuller hbij hη, Int.dvd_neg]

theorem valGauss_zero [P.LiesOver 𝒑] [𝓟.IsPrime] :
    valGauss hbij hζ 𝓟 0 = 0 :=
  valGauss_eq_zero hbij hζ hη 𝓟 0 <| Int.dvd_zero _

theorem valGauss_periodic [P.LiesOver 𝒑] {k : ℤ} (hk : ↑(p ^ f - 1 : ℕ) ∣ k) (a : ℤ) :
    valGauss hbij hζ 𝓟 (a + k) = valGauss hbij hζ 𝓟 a := by
  rw [valGauss, valGauss, GaussSum_periodic hbij hζ hη hk]

variable [IsCyclotomicExtension {p ^ f - 1} ℚ K]

theorem emultiplicity_smul_GaussSum [NeZero f] [IsCyclotomicExtension {p} ℚ F]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] [P.LiesOver 𝒑] [Fact (Odd p)] (σ : Gal(L/F)) :
    emultiplicity (σ • 𝓟) (span {(GaussSum hbij hζ 1 : 𝓞 L)}) =
      valGauss hbij hζ 𝓟 (galFEquiv p f K σ⁻¹).val.val := by
  rw [← emultiplicity_map_eq (Ideal.mapEquiv (MulSemiringAction.toRingEquiv Gal(L/F) (𝓞 L) σ⁻¹))
    (a := σ • 𝓟), mapEquiv_apply, mapEquiv_apply]
  erw [← pointwise_smul_def]
  rw [inv_smul_smul, valGauss, ← gal_gaussSum_eq_gaussSum hbij hζ hη σ⁻¹, map_span,
    Set.image_singleton, MulSemiringAction.toRingEquiv_apply]

variable [𝓟.IsPrime]

theorem valGauss_subadditive [NeZero 𝓟] [P.LiesOver 𝒑] (a b : ℤ) :
    valGauss hbij hζ 𝓟 (a + b) ≤ valGauss hbij hζ 𝓟 a + valGauss hbij hζ 𝓟 b := by
  have h𝓟 : Prime 𝓟 := prime_of_isPrime (NeZero.ne 𝓟) inferInstance
  by_cases h : ↑(p ^ f - 1 : ℕ) ∣ a + b
  · rw [valGauss_eq_zero hbij hζ hη 𝓟 _ h]
    exact zero_le _
  · rw [← emultiplicity_mul h𝓟, span_mul_span, Set.singleton_mul_singleton,
      GaussSum_mul_GaussSum _ _ _ _ h, ← Set.singleton_mul_singleton, ← span_mul_span,
      emultiplicity_mul h𝓟]
    exact self_le_add_right _ _

variable [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]

theorem valGauss_add_valGauss_sub_self [NeZero f] [𝓟.LiesOver 𝒑] [P.LiesOver 𝒑] {k : ℤ}
    (hk : ↑(p ^ f - 1 : ℕ) ∣ k) (a : ℤ) :
    valGauss hbij hζ 𝓟 a + valGauss hbij hζ 𝓟 (k - a) =
      if ↑(p ^ f - 1 : ℕ) ∣ a then 0 else f * (p - 1) := by
  have h₀ : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have : NeZero 𝓟 := ⟨ne_bot_of_liesOver_of_ne_bot h₀ _⟩
  have h𝓟 : Prime 𝓟 := prime_of_isPrime (NeZero.ne 𝓟) inferInstance
  have h₁ : Ideal.map (algebraMap ℤ (𝓞 L)) 𝒑 ≠ 0 := map_ne_bot_of_ne_bot h₀
  rw [show k - a = -a + k by ring, valGauss_periodic hbij hζ hη 𝓟 hk]
  split_ifs with h
  · rw [valGauss_eq_zero hbij hζ hη 𝓟 _ h, valGauss_eq_zero hbij hζ hη 𝓟 _ (by rwa [Int.dvd_neg]),
      zero_add, ENat.coe_zero]
  · rw [valGauss, valGauss, ← emultiplicity_mul h𝓟, span_mul_span, Set.singleton_mul_singleton,
      GaussSum_mul_GaussSum_neg hbij hζ _ h, ← Set.singleton_mul_singleton, ← span_mul_span,
      emultiplicity_mul h𝓟, emultiplicity_of_isUnit_right h𝓟.not_unit, zero_add, ← span_singleton_pow,
      emultiplicity_pow h𝓟, show (p : 𝓞 L) = algebraMap ℤ (𝓞 L) p by simp, ← Set.image_singleton,
      ← map_span, (FiniteMultiplicity.of_not_isUnit h𝓟.not_unit h₁).emultiplicity_eq_multiplicity,
      ← IsDedekindDomain.ramificationIdx_eq_multiplicity h₁, ramificationIdx_eq_p_sub_one f 𝓟,
      ENat.coe_mul]
    · infer_instance
    · rw [isUnit_iff, span_singleton_eq_top]
      exact RingHom.isUnit_map (algebraMap (𝓞 K) (𝓞 L)) <|
        isUnit_teichmuller_zpow_apply hbij (- a) isUnit_neg_one.unit

variable [IsCyclotomicExtension {p} ℚ F]

theorem exists_valGauss_add_valGauss_eq_valGauss_add_mul [NeZero f][𝓟.LiesOver P] [P.LiesOver 𝒑]
    (a b : ℤ) :
    ∃ k : ℕ,  valGauss hbij hζ 𝓟 a + valGauss hbij hζ 𝓟 b =
      valGauss hbij hζ 𝓟 (a + b) + k * (p - 1 : ℕ) := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have h₀ : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have : NeZero P := ⟨ne_bot_of_liesOver_of_ne_bot h₀ _⟩
  have : NeZero 𝓟 := ⟨ne_bot_of_liesOver_of_ne_bot h₀ _⟩
  have hP : Irreducible P := (prime_of_isPrime (NeZero.ne P) inferInstance).irreducible
  have h𝓟 : Prime 𝓟 := prime_of_isPrime (NeZero.ne 𝓟) inferInstance
  by_cases h : ↑(p ^ f - 1 : ℕ) ∣ a + b
  · obtain ⟨k, hb⟩ := h
    have hk : ↑(p ^ f - 1) ∣ ↑(p ^ f - 1) * k := Dvd.intro k rfl
    rw [add_comm, ← eq_sub_iff_add_eq] at hb
    rw [hb, valGauss_add_valGauss_sub_self hbij hζ hη 𝓟 hk, add_sub_cancel,
      valGauss_eq_zero hbij hζ hη 𝓟 _ hk, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul]
    split_ifs
    · simp
    · exact ⟨f, by simp⟩
  · by_cases ha : ↑(p ^ f - 1 : ℕ) ∣ a
    · rw [valGauss_eq_zero hbij hζ hη 𝓟 _ ha, zero_add, add_comm, valGauss_periodic hbij hζ hη 𝓟 ha]
      exact ⟨0, by simp⟩
    · by_cases hb : ↑(p ^ f - 1 : ℕ) ∣ b
      · rw [valGauss_eq_zero hbij hζ hη 𝓟 _ hb, add_zero, valGauss_periodic hbij hζ hη 𝓟 hb]
        exact ⟨0, by simp⟩
      · refine ⟨multiplicity P (span {JacobiSum hbij a b}), ?_⟩
        rw [valGauss, valGauss, ← emultiplicity_mul h𝓟, span_mul_span, Set.singleton_mul_singleton,
          GaussSum_mul_GaussSum _ _ _ _ h, ← Set.singleton_mul_singleton, ← span_mul_span,
          emultiplicity_mul h𝓟, ← Set.image_singleton (f := algebraMap (𝓞 K) (𝓞 L)), ← map_span,
          IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul' (v := P) hP h𝓟.irreducible
          (NeZero.ne _), ramificationIdx_eq_p_sub_one' p f, mul_comm,
          ← valGauss, FiniteMultiplicity.emultiplicity_eq_multiplicity]
        exact IsDedekindDomain.finiteMulticity IsPrime.ne_top'
          (by simpa using JacobiSum_ne_zero hbij hζ _ _ h ha hb)

omit hη [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] in
theorem one_le_valGauss [𝓟.LiesOver 𝒑] [P.LiesOver 𝒑] (a : ℤ) (ha : ¬ ↑(p ^ f - 1 : ℕ) ∣ a) :
    1 ≤ valGauss hbij hζ 𝓟 a := by
  rw [valGauss, ENat.one_le_iff_ne_zero, emultiplicity_ne_zero, dvd_span_singleton]
  exact GaussSum_mem hbij hζ 𝓟 _ ha

variable [NeZero f] [Fact (Odd p)]

omit hη in
theorem valGauss_one [𝓟.LiesOver P] [P.LiesOver 𝒑] :
    valGauss hbij hζ 𝓟 1 = 1 := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  rw [valGauss, show (1 : ℕ∞) = (1 : ℕ) by rfl, emultiplicity_eq_coe]
  constructor
  · rw [pow_one, dvd_span_singleton]
    apply GaussSum_mem hbij hζ 𝓟
    rw [Int.natCast_dvd_ofNat, Nat.dvd_one, Nat.pred_eq_succ_iff, zero_add]
    exact Nat.ne_of_lt' <| three_le_p_pow p f
  · rw [one_add_one_eq_two, dvd_span_singleton, ← Quotient.eq_zero_iff_mem, mk_sq_gausssum_eq,
      map_neg, ← map_one (algebraMap (𝓞 F) (𝓞 L)), ← map_sub, neg_eq_zero, Quotient.eq_zero_iff_mem]
    exact zeta_sub_one_not_mem_sq p f P hζ 𝓟

theorem exists_eq_valGauss_self_add_mul [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℕ) :
    ∃ k : ℕ, a = valGauss hbij hζ 𝓟 a + k * (p - 1 : ℕ) := by
  induction a with
  | zero => simp [valGauss_zero hbij hζ hη 𝓟]
  | succ n hn =>
      obtain ⟨k₁, h₁⟩ := hn
      obtain ⟨k₂, h₂⟩ := exists_valGauss_add_valGauss_eq_valGauss_add_mul hbij hζ hη 𝓟 n 1
      refine ⟨k₂ + k₁, ?_⟩
      rw [Nat.cast_add_one, h₁]
      rw [valGauss_one] at h₂
      rw [add_right_comm, h₂, add_assoc, ← add_mul]
      rw [← ENat.coe_add, Nat.cast_add_one]

theorem valGauss_le_self [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℕ) :
    valGauss hbij hζ 𝓟 a ≤ a := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have h₀ : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have : NeZero 𝓟 := ⟨ne_bot_of_liesOver_of_ne_bot h₀ _⟩
  induction a with
  | zero => simpa using valGauss_zero hbij hζ hη 𝓟
  | succ n hn =>
      rw [Nat.cast_add_one, Nat.cast_add_one]
      refine (valGauss_subadditive hbij hζ hη 𝓟 n 1).trans ?_
      rwa [valGauss_one, ENat.add_le_add_iff_right ENat.one_ne_top]

theorem valGauss_ne_top [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℕ) :
    valGauss hbij hζ 𝓟 a ≠ ⊤ :=
  lt_top_iff_ne_top.mp <| lt_of_le_of_lt (valGauss_le_self hbij hζ hη 𝓟 a) (ENat.coe_lt_top a)

theorem valGauss_toNat_eq_self [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℕ) (ha : a < p - 1) :
    (valGauss hbij hζ 𝓟 a).toNat = a := by
  rw [← ENat.coe_inj, ENat.coe_toNat_eq_self.mpr (valGauss_ne_top hbij hζ hη 𝓟 a)]
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have : 1 < p := hp.out.one_lt
  have : 1 ≤ f := NeZero.pos f
  cases a with
  | zero => simpa using valGauss_zero hbij hζ hη 𝓟
  | succ n =>
      obtain ⟨k, hk⟩ := exists_eq_valGauss_self_add_mul hbij hζ hη 𝓟 (n + 1 : ℕ)
      suffices k = 0 by
        rw [hk, this, Nat.cast_zero, zero_mul, add_zero]
      by_contra! h
      suffices k * (p - 1) + 1 ≤ n + 1 by
        refine (lt_iff_not_ge.mp (lt_of_le_of_lt this ha)) ?_
        nlinarith [Nat.one_le_iff_ne_zero.mpr h]
      rw [← ENat.coe_le_coe, Nat.cast_add_one, add_comm, ENat.coe_mul, hk,
        ENat.add_le_add_iff_right (ENat.coe_toNat_eq_self.mp rfl)]
      refine one_le_valGauss hbij hζ 𝓟 (n + 1 : ℕ) ?_
      rw [Int.natCast_dvd_natCast]
      apply Nat.not_dvd_of_pos_of_lt n.succ_pos
      exact lt_of_lt_of_le ha (by bound)

theorem valGauss_toNat_p_sub_one [𝓟.LiesOver P] [P.LiesOver 𝒑] (hf : 2 ≤ f) :
    (valGauss hbij hζ 𝓟 (p - 1 : ℕ)).toNat = p - 1 := by
  rw [← ENat.coe_inj, ENat.coe_toNat_eq_self.mpr (valGauss_ne_top hbij hζ hη 𝓟 _)]
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  obtain ⟨k, hk⟩ := exists_eq_valGauss_self_add_mul hbij hζ hη 𝓟 (p - 1 : ℕ)
  suffices k = 0 by
    rwa [this, Nat.cast_zero, zero_mul, add_zero, ENat.coe_sub, Nat.cast_one, eq_comm] at hk
  by_contra! h
  suffices 1 + k * (p - 1) ≤ p - 1 by nlinarith [Nat.one_le_iff_ne_zero.mpr h]
  rw [← ENat.coe_le_coe, hk, ENat.coe_add, ENat.coe_mul, Nat.cast_one]
  gcongr
  refine one_le_valGauss hbij hζ 𝓟 _ ?_
  rw [Int.natCast_dvd_natCast]
  refine Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_iff_lt.mpr hp.out.one_lt) ?_
  rw [Nat.lt_sub_iff_add_lt, Nat.sub_add_cancel hp.out.one_le]
  exact lt_self_pow₀ hp.out.one_lt hf

theorem valGauss_le_sum_digits_aux [𝓟.LiesOver P] [P.LiesOver 𝒑] (L : List ℕ) :
    valGauss hbij hζ 𝓟 (Nat.ofDigits p L : ℕ) ≤ L.sum := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have h₀ : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have : NeZero 𝓟 := ⟨ne_bot_of_liesOver_of_ne_bot h₀ _⟩
  induction L with
  | nil => simpa [Nat.ofDigits] using valGauss_zero hbij hζ hη 𝓟
  | cons head tail ih =>
      rw [List.sum_cons, Nat.cast_add, Nat.ofDigits_cons, Nat.cast_add]
      refine (valGauss_subadditive hbij hζ hη 𝓟 _ _).trans ?_
      gcongr
      · exact valGauss_le_self hbij hζ hη ..
      · rwa [Nat.cast_mul, valGauss_frob]

theorem valGauss_toNat_le_sum_digits [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℕ) :
    (valGauss hbij hζ 𝓟 a).toNat ≤ (Nat.digits p a).sum := by
  apply ENat.toNat_le_of_le_coe
  convert valGauss_le_sum_digits_aux hbij hζ hη 𝓟 (Nat.digits p a)
  rw [Nat.ofDigits_digits]

theorem two_mul_sum_valGauss_toNat' [𝓟.LiesOver P] [P.LiesOver 𝒑] :
    2 * ∑ a ∈ Finset.range (p ^ f), (valGauss hbij hζ 𝓟 a).toNat =
      (p ^ f - 2) * f * (p - 1) := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  rw [← ENat.coe_inj, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat]
  simp_rw [ENat.coe_toNat_eq_self.mpr (valGauss_ne_top hbij hζ hη 𝓟 _)]
  have h : 1 ≤ p ^ f := NeZero.one_le
  rw [two_mul, ← Fin.sum_univ_eq_sum_range, show p ^ f = p ^ f - 1 + 1 by rw [Nat.sub_add_cancel h]]
  nth_rewrite 2 [← Equiv.sum_comp Fin.revPerm]
  rw [← Finset.sum_add_distrib]
  simp_rw [Fin.revPerm_apply, Fin.val_rev, Nat.reduceSubDiff, Nat.cast_sub (Fin.is_le _),
    valGauss_add_valGauss_sub_self hbij hζ hη 𝓟 dvd_rfl, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul,
    Int.natCast_dvd_natCast]
  rw [← Finset.univ.sum_erase_add _ (Finset.mem_univ 0),
    ← Finset.sum_erase_add _ _ (a := Fin.ofNat (p ^ f - 1 + 1) (p ^ f - 1)) (by aesop),
    Finset.sum_ite_of_false, Finset.sum_const, Finset.card_erase_of_mem (by aesop),
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin,
    add_tsub_cancel_right, nsmul_eq_mul, if_pos (by aesop), if_pos (by aesop),
    add_zero, add_zero, mul_assoc]
  intro x hx
  simp at hx
  exact Nat.not_dvd_of_pos_of_lt (by grind) (by grind)

theorem two_mul_sum_valGauss_toNat [𝓟.LiesOver P] [P.LiesOver 𝒑] :
    2 * ∑ a ∈ Finset.range (p ^ f - 1), (valGauss hbij hζ 𝓟 a).toNat =
      f * (p - 1) * (p ^ f - 2) := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  rw [← Finset.sum_insert_of_eq_zero_if_notMem (a := p ^ f - 1), ← Finset.range_add_one,
        Nat.sub_add_cancel NeZero.one_le, ← ENat.coe_inj, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat]
  · simp_rw [ENat.coe_toNat_eq_self.mpr (valGauss_ne_top hbij hζ hη 𝓟 _)]
    have h : 1 ≤ p ^ f := NeZero.one_le
    rw [two_mul, ← Fin.sum_univ_eq_sum_range, show p ^ f = p ^ f - 1 + 1 by rw [Nat.sub_add_cancel h]]
    nth_rewrite 2 [← Equiv.sum_comp Fin.revPerm]
    rw [← Finset.sum_add_distrib]
    simp_rw [Fin.revPerm_apply, Fin.val_rev, Nat.reduceSubDiff, Nat.cast_sub (Fin.is_le _),
      valGauss_add_valGauss_sub_self hbij hζ hη 𝓟 dvd_rfl, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul,
      Int.natCast_dvd_natCast]
    rw [← Finset.univ.sum_erase_add _ (Finset.mem_univ 0),
      ← Finset.sum_erase_add _ _ (a := Fin.ofNat (p ^ f - 1 + 1) (p ^ f - 1)) (by aesop),
      Finset.sum_ite_of_false, Finset.sum_const, Finset.card_erase_of_mem (by aesop),
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin,
      add_tsub_cancel_right, nsmul_eq_mul, if_pos (by aesop), if_pos (by aesop),
      add_zero, add_zero, Nat.cast_comm]
    intro x hx
    simp at hx
    exact Nat.not_dvd_of_pos_of_lt (by grind) (by grind)
  · intro _
    rw [valGauss_eq_zero hbij hζ hη 𝓟 _ dvd_rfl, ENat.toNat_zero]

theorem valGauss_toNat_eq_sum_digits [𝓟.LiesOver P] [P.LiesOver 𝒑] (a : ℕ) (ha : a ≤ p ^ f - 2) :
    (valGauss hbij hζ 𝓟 a).toNat = (Nat.digits p a).sum := by
  revert a
  simp_rw [← Finset.mem_range_succ_iff, Nat.succ_eq_add_one, show p ^ f - 2 + 1 = p ^ f - 1 by
    rw [Nat.sub_succ', Nat.sub_add_cancel (NeZero.one_le)]]
  refine (Finset.sum_eq_sum_iff_of_le fun a _ ↦ valGauss_toNat_le_sum_digits hbij hζ hη 𝓟 a).mp ?_
  rw [← Nat.add_right_cancel_iff (n := (p.digits (p ^ f - 1)).sum), ← Nat.mul_right_inj two_ne_zero,
    eq_comm]
  calc
    _ = f * p ^ (f - 1) * (p * (p - 1)) := by
      rw [← Finset.sum_range_succ, Nat.sub_add_cancel NeZero.one_le,
        Nat.sum_sum_digits_eq hp.out.one_lt, Nat.choose_two_right, mul_rotate',
        Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one p)]
    _ = f * (p - 1) * (p ^ f - 2) + 2 * (p.digits (p ^ f - 1)).sum := by
      rw [Nat.digits_pow_sub_one hp.out.one_lt, List.sum_replicate, smul_eq_mul, mul_comm 2,
        ← mul_add, Nat.sub_add_cancel (Nat.le_of_succ_le (three_le_p_pow p f)), ← mul_assoc,
        mul_assoc f, ← Nat.pow_add_one, Nat.sub_add_cancel NeZero.one_le, Nat.mul_right_comm]
    _ = 2 * (∑ i ∈ Finset.range (p ^ f - 1), (valGauss hbij hζ 𝓟 i).toNat +
        (p.digits (p ^ f - 1)).sum) := by
      rw [mul_add, two_mul_sum_valGauss_toNat hbij hζ hη]

