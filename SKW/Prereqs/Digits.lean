module

public import Mathlib.Data.List.Indexes
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

@[expose] public section

/-! ### Finset / MulAction -/

@[to_additive]
theorem Finset.prod_filter_eq_eq_pow_card {α β γ : Type*} [Fintype α] [CommMonoid γ]
    [DecidableEq β] (f : α → β) (b : β) (g : β → γ) :
    ∏ x with b = f x, g (f x) = g b ^ Fintype.card {x // b = f x} := by
  rw [Finset.pow_eq_prod_const, Finset.prod_range,
    Finset.prod_subtype (p := fun x ↦ b = f x) _ (by simp)]
  exact Fintype.prod_equiv (Fintype.equivFin _) _ _ fun x ↦ by rw [← x.prop]

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst {α β : Type*} [Group α]
    [MulAction α β] (b : β) (a : α) :
    ((MulAction.orbitProdStabilizerEquivGroup α b).symm a).1 = a • b := rfl

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_apply_smul {α β : Type*} [Group α]
    [MulAction α β] (b : β) (x : orbit α b) (y : stabilizer α b) :
    MulAction.orbitProdStabilizerEquivGroup α b (x, y) • b = x := by
  rw [← MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst, Equiv.symm_apply_apply]

/-! ### List / Nat.digits -/

theorem List.mapIdx_replicate {α β : Type*} (f : ℕ → α → β) (n : ℕ) (a : α) :
    mapIdx f (replicate n a) = map (fun n ↦ f n a) (range n) := by
  induction n with
  | zero => simp
  | succ n hn => simp [replicate_succ', mapIdx_append, range_succ, hn]

theorem Nat.digits_base_pow_sub_one {b : ℕ} (hb : 1 < b) (l : ℕ) :
    b.digits (b ^ l - 1) = List.replicate l (b - 1) := by
  suffices b ^ l - 1 = Nat.ofDigits b (List.replicate l (b - 1)) by
    rw [this, Nat.digits_ofDigits _ hb _ (by grind) (by grind)]
  induction l with
    | zero => simp
    | succ l hl =>
        rw [List.replicate_succ, Nat.ofDigits_cons, ← hl, add_comm (b - 1), Nat.mul_sub, mul_one,
          ← Nat.pow_succ', ← Nat.add_sub_assoc hb.le,
          Nat.sub_add_cancel (Nat.le_self_pow l.succ_ne_zero b)]

theorem Nat.digits_eq_replicate_base_sub_one_iff {b : ℕ} (hb : 1 < b) (n k : ℕ) :
    b.digits n = List.replicate k (b - 1) ↔ n = b ^ k - 1 := by
  refine ⟨?_, fun h ↦ by rw [h, digits_base_pow_sub_one hb]⟩
  intro h
  have := congr_arg (Nat.ofDigits b) h
  rwa [ofDigits_digits, ← digits_base_pow_sub_one hb, ofDigits_digits] at this

theorem Nat.digitsAppend_def (b l n : ℕ) :
    Nat.digitsAppend b l n = b.digits n ++ List.replicate (l - (b.digits n).length) 0 := by
  sorry

theorem Nat.digitsAppend_eq_nil_iff {b l n : ℕ} :
    Nat.digitsAppend b l n = [] ↔ n = 0 ∧ l = 0 := by
  rw [digitsAppend_def, List.append_eq_nil_iff, digits_eq_nil_iff_eq_zero,
    List.replicate_eq_nil_iff, Nat.sub_eq_zero_iff_le, and_congr_right_iff]
  intro h
  rw [h, digits_zero, List.length_nil, le_zero]

theorem Nat.mem_digitsAppend_of_mem_digits {b n : ℕ} (l d : ℕ) (hd : d ∈ b.digits n) :
    d ∈ b.digitsAppend l n := by
  rw [digitsAppend_def, List.mem_append]
  exact Or.inl hd

theorem Nat.digitsAppend_sum_eq_digits_sum (b l n : ℕ) :
    (Nat.digitsAppend b l n).sum = (Nat.digits b n).sum := by
  rw [Nat.digitsAppend_def, List.sum_append, List.sum_replicate, nsmul_zero, add_zero]

theorem Nat.digitsAppend_eq_digits_iff {b l n : ℕ} (hn : n ≠ 0) (p : b.digitsAppend l n ≠ []) :
    b.digitsAppend l n = b.digits n ↔ (b.digitsAppend l n).getLast p ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw! [h]
    exact Nat.getLast_digit_ne_zero _ hn
  · contrapose! h
    rw [ne_eq, b.digitsAppend_def, List.append_right_eq_self, List.replicate_eq_nil_iff] at h
    rw! [b.digitsAppend_def]
    rw [List.getLast_append_right, List.getLast_replicate]
    rwa [ne_eq, List.replicate_eq_nil_iff]

theorem Nat.eq_mapIdx_digits_sum (b n : ℕ) :
    n = (List.mapIdx (fun i a ↦ a * b ^ i) (b.digits n)).sum := by
  convert Nat.ofDigits_eq_sum_mapIdx b (b.digits n)
  rw [Nat.ofDigits_digits]

theorem Nat.eq_sum_digits_mul_pow (b n : ℕ) :
    n = ∑ i : Fin (b.digits n).length, (b.digits n)[i] * b ^ i.val := by
  convert Nat.eq_mapIdx_digits_sum b n
  simp [List.mapIdx_eq_zipIdx_map, ← Fin.sum_univ_fun_getElem,
      ← Fin.sum_congr' _ List.length_zipIdx.symm]

theorem Nat.eq_mapIdx_digitsAppend_sum (b l n : ℕ) :
    n = (List.mapIdx (fun i a ↦ a * b ^ i) (b.digitsAppend l n)).sum := by
  simpa [digitsAppend_def, List.mapIdx_append, List.mapIdx_replicate] using Nat.eq_mapIdx_digits_sum b n

theorem Nat.eq_sum_digitsAppend_mul_pow {b n : ℕ} (l : ℕ) (hb : 1 < b) (hn : n < b ^ l):
    haveI : (b.digitsAppend l n).length = l := length_digitsAppend hb l hn
    n = ∑ i : Fin l, (b.digitsAppend l n)[i] * b ^ i.val := by
  convert Nat.eq_mapIdx_digitsAppend_sum b l n
  simp [List.mapIdx_eq_zipIdx_map, ← Fin.sum_univ_fun_getElem,
    ← Fin.sum_congr' _ (List.length_zipIdx.trans (length_digitsAppend hb l hn)).symm]

theorem Nat.sub_one_mul_sum_fract_div_eq_digits_sum (b l a : ℕ) (hb : 1 < b) [NeZero l]
    (ha : a < b ^ l - 1) :
    (b - 1) * ∑ j ∈ Finset.range l, Int.fract (b ^ j * a / (b ^ l - 1 : ℕ) : ℚ) =
      (Nat.digits b a).sum := by
  by_cases h₀ : a = 0
  · simp [h₀]
  have : 1 < b ^ l := Nat.one_lt_pow (NeZero.ne _) hb
  have : 1 < (b : ℚ) ^ l := by rwa [← Nat.cast_pow, Nat.one_lt_cast]
  have ha' : a < b ^ l := by grind
  let L' := b.digitsAppend l a
  have hL : (b.digitsAppend l a).length = l := Nat.length_digitsAppend hb l ha'
  rw [← Nat.digitsAppend_sum_eq_digits_sum b l, Finset.sum_range]
  have {j : Fin l} : Int.fract (b ^ j.val * a / (b ^ l - 1 : ℕ) : ℚ) =
      (∑ i : Fin l, (b.digitsAppend l a)[i] * b ^ (j + i).val) / (b ^ l - 1) := by
    refine Int.fract_eq_iff.mpr ⟨?_, ?_, ?_⟩
    · bound
    · refine (Rat.div_lt_iff ?_).mpr ?_
      · positivity
      · rw [one_mul, ← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_sub (by grind), Rat.natCast_lt_natCast]
        · obtain ⟨i₀, h₀⟩ : ∃ i : Fin l, (b.digitsAppend l a)[i] < b - 1 := by
            suffices ∃ d ∈ b.digitsAppend l a, d < b - 1 by
              obtain ⟨d, hd₁, hd₂⟩ := this
              rw [List.mem_iff_get] at hd₁
              obtain ⟨i₀, rfl⟩ := hd₁
              exact ⟨(finCongr hL) i₀, by simpa⟩
            contrapose! ha
            have : b.digits a = List.replicate l (b - 1) := by
              rw [List.eq_replicate_iff]
              refine ⟨?_, ?_⟩
              · have : b.digitsAppend l a ≠ [] := by
                  rw [ne_eq, Nat.digitsAppend_eq_nil_iff, not_and_or]
                  exact Or.inl h₀
                rw [← (Nat.digitsAppend_eq_digits_iff h₀ this).mpr,
                  Nat.length_digitsAppend hb l ha']
                specialize ha _ (List.getLast_mem this)
                grind
              · intro d hd
                refine le_antisymm ?_ ?_
                · rw [Nat.le_iff_lt_add_one, Nat.sub_add_cancel hb.le]
                  exact Nat.digits_lt_base hb hd
                · apply ha
                  exact Nat.mem_digitsAppend_of_mem_digits l d hd
            rw [Nat.digits_eq_replicate_base_sub_one_iff hb] at this
            rw [this]
          rw [← Equiv.sum_comp (Equiv.addRight j).symm]
          simp only [Equiv.addRight_symm, Equiv.coe_addRight, Fin.getElem_fin,
            add_neg_cancel_comm_assoc]
          have : b ^ l - 1 = ∑ i : Fin l, (b - 1) * b ^ i.val := by
            rw [← Finset.mul_sum, mul_comm, ← Finset.sum_range, geom_sum_mul_of_one_le hb.le]
          rw [this]
          refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀ + j, Finset.mem_univ _, ?_⟩
          · gcongr
            rw [Nat.le_iff_lt_add_one, Nat.sub_add_cancel hb.le]
            exact Nat.lt_of_mem_digitsAppend hb l _ <| List.mem_of_getElem rfl
          · refine mul_lt_mul_of_pos_right (by simpa) (by positivity)
    rw [Nat.cast_sub, Nat.cast_pow, Nat.cast_one, ← sub_div]
    suffices (b ^ l - 1 : ℤ) ∣ b ^ j.val * a -
        ∑ i : Fin l, (b.digitsAppend l a)[i] * b ^ (i + j).val by
      obtain ⟨c, hc⟩ := this
      refine ⟨c, ?_⟩
      rw [div_eq_iff, mul_comm (c : ℚ)]
      simp_rw [add_comm j]
      exact_mod_cast hc
      grind
    rw [congr_arg ((↑) : ℕ → ℤ) <| Nat.eq_sum_digitsAppend_mul_pow l hb ha', Nat.cast_sum,
      Finset.mul_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ ↦ ?_
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, mul_comm, mul_assoc, ← pow_add,
      ← mul_sub, Fin.val_add]
    nth_rewrite 1 [← Nat.mod_add_div (i + j) l, pow_add]
    rw [← _root_.mul_sub_one, ← mul_assoc]
    refine Int.dvd_mul_of_dvd_right ?_
    exact pow_one_sub_dvd_pow_mul_sub_one _ _ _
    bound
  simp_rw [this, Fin.getElem_fin, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ← Finset.sum_div]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, 1, 2, k]
    rw [← Equiv.sum_comp (Equiv.addRight k).symm, ← Finset.mul_sum]
    simp only [Equiv.addRight_symm_apply, neg_add_cancel_right, ← Finset.sum_range,
      geom_sum_eq (Nat.cast_ne_one.mpr hb.ne')]
  rw [← Finset.sum_mul, mul_div_assoc, div_div_cancel_left', mul_comm, mul_assoc, inv_mul_cancel₀,
    mul_one, Nat.cast_list_sum, ← Fin.sum_univ_fun_getElem, ← Fin.sum_congr' _ hL]
  rfl
  · rw [sub_ne_zero, Nat.cast_ne_one]
    exact hb.ne'
  grind

/-! ### ArithmeticFunction.phi -/

def ArithmeticFunction.phi : ArithmeticFunction ℤ where
  toFun n := Nat.totient n
  map_zero' := by simp

@[simp]
theorem ArithmeticFunction.phi_apply (n : ℕ) :
    phi n = Nat.totient n := rfl

open Nat in
theorem ArithmeticFunction.isMultiplicative_phi :
    IsMultiplicative phi :=
  IsMultiplicative.iff_ne_zero.mpr ⟨by simp, fun _ _ h ↦ by simp [Nat.totient_mul h]⟩

theorem Nat.totient_mul_totient_eq (m n : ℕ) :
    totient m * totient n = totient (lcm m n) * totient (gcd m n) := by
  have :=  ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply
    ArithmeticFunction.isMultiplicative_phi (x := m) (y := n)
  rwa [ArithmeticFunction.phi_apply, ArithmeticFunction.phi_apply, ArithmeticFunction.phi_apply,
    ArithmeticFunction.phi_apply, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_inj, eq_comm] at this
