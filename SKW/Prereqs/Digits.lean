module

public import Mathlib.Data.List.Indexes
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

set_option linter.style.header false

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

theorem Nat.digits_eq_replicate_base_sub_one_iff {b : ℕ} (hb : 1 < b) {n k : ℕ} :
    b.digits n = List.replicate k (b - 1) ↔ n = b ^ k - 1 := by
  refine ⟨?_, fun h ↦ by rw [h, digits_base_pow_sub_one hb]⟩
  intro h
  have := congr_arg (Nat.ofDigits b) h
  rwa [ofDigits_digits, ← digits_base_pow_sub_one hb, ofDigits_digits] at this

theorem Nat.ofDigits_eq_base_pow_length_sub_one_iff {b : ℕ} {L : List ℕ} (hb : 1 < b)
    (hL : ∀ x ∈ L, x < b) :
    ofDigits b L = b ^ L.length - 1 ↔ L = List.replicate L.length (b - 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← (setInvOn_digitsAppend_ofDigits hb L.length).1 ⟨rfl, hL⟩,
      digitsAppend_eq_digits_iff_le.mpr,
      (digits_eq_replicate_base_sub_one_iff hb).mpr h,  List.length_replicate]
    rw [h, digits_base_pow_sub_one hb, List.length_replicate]
  · rw [← ofDigits_digits b (b ^ L.length - 1), digits_base_pow_sub_one hb L.length, ← h]

theorem Nat.ofDigits_eq_sum (b : ℕ) (L : List ℕ) :
    ofDigits b L = ∑ i : Fin L.length, L[i] * b ^ (i : ℕ) := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp [List.mapIdx_eq_zipIdx_map, ← Fin.sum_univ_fun_getElem,
    ← Fin.sum_congr' _ List.length_zipIdx.symm]

theorem Nat.eq_sum_digits_mul_pow (b n : ℕ) :
    n = ∑ i : Fin (b.digits n).length, (b.digits n)[i] * b ^ i.val :=
  (ofDigits_digits b n).symm.trans (ofDigits_eq_sum b _)

/- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
TODO, CHANGE BACK WHEN UPSTREAMING to `Mathlib/Data/Nat/Digits/Lemmas.lean`: there `digitsAppend`
is visible, and the intended proof of `Nat.ofDigits_digitsAppend` is
  `rw [digitsAppend, ofDigits_append_replicate_zero, ofDigits_digits]`.
The proof below via `mapIdx` is only a workaround, because `digitsAppend` does not expose its body
here (it replaces the stub `Nat.digitsAppend_def`, whose `sorry` leaked into the axioms).
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! -/
theorem Nat.ofDigits_digitsAppend (b l n : ℕ) : ofDigits b (digitsAppend b l n) = n := by
  rw [ofDigits_eq_sum_mapIdx, mapIdx_digitsAppend_sum_eq]

theorem Nat.eq_sum_digitsAppend_mul_pow {b n : ℕ} (l : ℕ) (hb : 1 < b) (hn : n < b ^ l) :
    haveI : (b.digitsAppend l n).length = l := length_digitsAppend hb l hn
    n = ∑ i : Fin l, (b.digitsAppend l n)[i] * b ^ i.val := by
  nth_rw 1 [← (setInvOn_digitsAppend_ofDigits hb l).2 hn]
  rw [ofDigits_eq_sum, ← Fin.sum_congr' _ (length_digitsAppend hb l hn)]
  rfl

/-- Multiplying by `b` modulo `b ^ L.length - 1` rotates the digits of `L` to the right by one
place. -/
theorem Nat.ofDigits_mul_modEq {b : ℕ} (hb : 0 < b) (L : List ℕ) :
    b * ofDigits b L ≡ ofDigits b (L.rotate (L.length - 1)) [MOD b ^ L.length - 1] := by
  obtain rfl | ⟨L', c, rfl⟩ := L.eq_nil_or_concat
  · simp [Nat.ofDigits_nil]
  rw [List.concat_eq_append, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.rotate_append_length_eq, ofDigits_append, ofDigits_append, ofDigits_singleton,
    List.length_singleton, pow_one, mul_add, ← mul_assoc, ← pow_succ',
    ← Nat.sub_add_cancel (by grind : 1 ≤ b ^ L'.length.succ), add_mul, one_mul, ← add_assoc,
    ← add_rotate]
  exact add_modulus_mul_modEq_iff.mpr rfl

/-- Multiplying by `b ^ i` modulo `b ^ L.length - 1` rotates the digits of `L` to the right by `i`
places. -/
theorem Nat.ofDigits_mul_pow_modEq {b : ℕ} (hb : 0 < b) (L : List ℕ) {i : ℕ} (hi : i ≤ L.length) :
     b ^ i * ofDigits b L ≡ ofDigits b (L.rotate (L.length - i)) [MOD b ^ L.length - 1] := by
  induction i with
  | zero => simpa using ofDigits_modEq' b b _ rfl L
  | succ n hn =>
    have h := (Nat.ModEq.mul_left b (hn (by lia))).trans <|
      (List.length_rotate _ _) ▸ Nat.ofDigits_mul_modEq hb _
    rwa [← mul_assoc, ← pow_succ', List.rotate_rotate, tsub_add_eq_add_tsub (by lia),
      add_tsub_assoc_of_le (by lia), ← List.rotate_rotate, List.rotate_length,
      ← tsub_add_eq_tsub_tsub_swap] at h

theorem List.sum_getElem_rotate {R : Type*} [AddCommMonoid R] (L : List R) (x : Fin L.length) :
    ∑ i : Fin L.length, (L.rotate i)[x] = L.sum := by
  have : NeZero L.length := Fin.neZero x
  rw [← (Equiv.sum_comp (Equiv.addLeft x) fun i ↦ L[i]).trans (Fin.sum_univ_getElem L)]
  simp [Fin.val_add, List.getElem_rotate]

/-- Adding up all the rotations of `L` puts each digit once in each position. -/
theorem Nat.sum_ofDigits_rotate (b : ℕ) (L : List ℕ) :
    ∑ i ∈ Finset.range L.length, Nat.ofDigits b (L.rotate i) =
      L.sum * ∑ i ∈ Finset.range L.length, b ^ i := by
  simp_rw [Nat.ofDigits_eq_sum, ← Fin.sum_congr' _ (L.length_rotate _).symm, Fin.val_cast,
    Fin.getElem_fin, Fin.val_cast]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, Finset.sum_range, ← Fin.getElem_fin,  List.sum_getElem_rotate,
    Finset.mul_sum]

/-- If the digits of `L` are not all equal to `b - 1`, the same holds for any rotation of `L`. -/
theorem Nat.ofDigits_rotate_lt {b : ℕ} {L : List ℕ} (hb : 1 < b) (hL : ∀ x ∈ L, x < b)
    (hx : ofDigits b L < b ^ L.length - 1) (n : ℕ) :
    ofDigits b (L.rotate n) < b ^ L.length - 1 := by
  contrapose! hx
  obtain hl | hl := L.length.eq_zero_or_pos
  · simp [hl]
  refine le_of_eq ?_
  rw [eq_comm, ofDigits_eq_base_pow_length_sub_one_iff hb hL, ← List.rotate_eq_rotate,
    List.rotate_replicate, ← List.length_rotate _ n,
    ← ofDigits_eq_base_pow_length_sub_one_iff hb (by simpa [List.mem_rotate]),
    List.length_rotate, (LE.le.ge_iff_eq hx).mp]
  exact le_sub_one_of_lt <|
    List.length_rotate _ _ ▸ ofDigits_lt_base_pow_length hb (by simpa [List.mem_rotate])

theorem Nat.sub_one_mul_sum_mod_eq {b l x : ℕ} (hb : 1 < b) (hx : x < b ^ l - 1) :
    (b - 1) * ∑ i ∈ Finset.range l, x * b ^ i % (b ^ l - 1) =
      (b ^ l - 1) * (Nat.digits b x).sum := by
  let L := Nat.digitsAppend b l x
  have hl : (b.digitsAppend l x).length = l := by rw [length_digitsAppend hb _ (by lia)]
  calc
    _ = (b - 1) * ∑ i ∈ Finset.range l, b ^ i * ofDigits b L % (b ^ l - 1) := by
      simp_rw [mul_comm x, L, ofDigits_digitsAppend b l x]
    _ = (b - 1) * ∑ i ∈ Finset.range l, ofDigits b (L.rotate (L.length - i)) := by
      refine congr_arg ((b - 1) * ·) <| Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hl, ofDigits_mul_pow_modEq (by lia) _ (by grind)]
      refine mod_eq_of_lt (ofDigits_rotate_lt hb (fun _ hx ↦ lt_of_mem_digitsAppend hb _ _ hx) ?_ _)
      rwa [ofDigits_digitsAppend, hl]
    _ = (b - 1) * ∑ i ∈ Finset.range l, ofDigits b (L.rotate i) := by
      rw [Finset.sum_range, Finset.sum_range]
      nth_rewrite 2 [← Equiv.sum_comp (Equiv.neg (Fin _))]
      congr with i
      rw [Equiv.neg_apply, Fin.val_neg', ← List.rotate_mod L, hl]
    _ = L.sum * (∑ i ∈ Finset.range L.length, b ^ i) * (b - 1) := by
      rw [← sum_ofDigits_rotate, mul_comm, hl]
    _ = (b ^ l - 1) * (b.digits x).sum := by
      rw [digitsAppend_sum_eq_digits_sum, mul_assoc, geom_sum_mul_of_one_le hb.le, hl, mul_comm]

theorem Nat.sub_one_mul_sum_fract_div_eq_digits_sum {b l a : ℕ} (hb : 1 < b) [NeZero l]
    (ha : a ≤ b ^ l - 2) :
    (b - 1) * ∑ j ∈ Finset.range l, Int.fract (b ^ j * a / (b ^ l - 1 : ℕ) : ℚ) =
      (Nat.digits b a).sum := by
  by_cases h₀ : a = 0
  · simp [h₀]
  have hb' : 1 < b ^ l := Nat.one_lt_pow (NeZero.ne _) hb
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
      · rw [one_mul, ← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_sub (by grind),
        Rat.natCast_lt_natCast]
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
                rw [← (Nat.digitsAppend_eq_digits_iff h₀).mpr,
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
            exact sub_succ_lt_self (b ^ l) 1 hb'
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
    · suffices (b ^ l - 1 : ℤ) ∣ b ^ j.val * a -
          ∑ i : Fin l, (b.digitsAppend l a)[i] * b ^ (i + j).val by
        obtain ⟨c, hc⟩ := this
        refine ⟨c, ?_⟩
        rw [div_eq_iff, mul_comm (c : ℚ)]
        · simp_rw [add_comm j]
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
  · rfl
  · rw [sub_ne_zero, Nat.cast_ne_one]
    exact hb.ne'
  grind

theorem mul_fract_div_eq_mod (a b : ℤ) (hb : 0 < b) :
    b * Int.fract ((a / b : ℚ)) = (a % b : ℤ) := by
  rw [Int.fract, mul_sub, mul_div_cancel₀ _ (by aesop), ← Int.cast_mul, ← Int.cast_sub,
    Int.cast_inj,
    eq_comm, mul_comm]
  refine (Int.emod_eq_iff hb.ne').mpr ⟨?_, ?_, ?_⟩
  · have := Int.sub_floor_div_mul_nonneg (a : ℚ) (b := (b : ℚ)) ?_
    · exact_mod_cast this
    · exact_mod_cast hb
  · have := Int.sub_floor_div_mul_lt (a : ℚ) (b := (b : ℚ)) ?_
    · rw [Int.natAbs_of_nonneg hb.le]
      exact_mod_cast this
    exact_mod_cast hb
  · rw [sub_sub_cancel_left, Int.dvd_neg, mul_comm]
    exact Int.dvd_mul_right b _
