module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.Ideals
public import SKW.Prereqs.CyclotomicField
public import SKW.Prereqs.Instances
public import SKW.Prereqs.IntermediateField
public import SKW.Prereqs.TameRamification

@[expose] public section

/-!
# Reduction steps for Kronecker-Weber

This file establishes the reduction steps that allow us to prove Kronecker-Weber by induction:

1. `kw_cyclic_compositum`: If two cyclic `p`-extensions have cyclic compositum, one contains the
   other.
2. `kw_minkowski`: Every non-trivial extension of `ℚ` is ramified at some finite prime.
3. `kw_ramification_reduction`: Given `K/ℚ` cyclic of prime power degree with `q ≠ p` ramified,
   there exists a cyclotomic `L/ℚ` such that `KL = FL` for `F/ℚ` cyclic of prime power degree
   with `q` unramified.

The decomposition of a finite abelian extension into cyclic prime power subextensions is
`IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top` (in `SKW/Prereqs/IntermediateField.lean`).
The reduction of the general (abelian) case to the cyclic prime power case
(`kw_reduce_to_prime_power`) lives in `KroneckerWeber.lean`, in `IntermediateField ℚ A` currency.
-/

open NumberField Ideal Pointwise Module IntermediateField

noncomputable section

/-- `K/ℚ` is a cyclic Galois extension of prime power degree (`> 1`). -/
def IsCyclicOfPrimePowDegree (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  IsGalois ℚ K ∧ IsCyclic Gal(K/ℚ) ∧ IsPrimePow (Module.finrank ℚ K)

variable {p : ℕ} [hp : Fact p.Prime]

/- Superseded by the ambient (`IntermediateField ℚ A`) form below, which callers use without
restricting into the compositum.
/-- Two cyclic `p`-extensions of `ℚ` whose compositum is cyclic must be comparable. -/
lemma kw_cyclic_compositum (L : Type*) [Field L] [NumberField L] (K K' : IntermediateField ℚ L)
    (h : finrank ℚ K ∣ finrank ℚ K') [IsGalois ℚ L] [hCL : IsCyclic Gal(L/ℚ)] :
    K ≤ K' := by
  rw [← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/ℚ) ℚ L K,
    ← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/ℚ) ℚ L K']
  apply IsGaloisGroup.fixedPoints_le_of_le
  rw [IsCyclic.subgroup_le_subgroup_iff, IsGaloisGroup.card_fixingSubgroup_eq_finrank,
    IsGaloisGroup.card_fixingSubgroup_eq_finrank]
  have hd : finrank ℚ K ∣ finrank ℚ L := finrank_mul_finrank ℚ K L ▸ dvd_mul_right _ _
  have hd' : finrank ℚ K' ∣ finrank ℚ L := finrank_mul_finrank ℚ K' L ▸ dvd_mul_right _ _
  have he : finrank K L = finrank ℚ L / finrank ℚ K :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  have he' : finrank K' L = finrank ℚ L / finrank ℚ K' :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  rwa [he, he', Nat.div_dvd_div_iff finrank_pos finrank_pos hd' hd]
-/

/-- Every non-trivial extension of `ℚ` is ramified at some finite prime (Minkowski). -/
lemma kw_minkowski (K : Type*) [Field K] [NumberField K] (h : Module.finrank ℚ K > 1) :
    ∃ q : ℕ, q.Prime ∧ ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsMaximal ∧ 𝔮.LiesOver (Ideal.span {(q : ℤ)}) ∧
      1 < Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) 𝔮 := by
  obtain ⟨𝔮, hq, hq'⟩ := exists_not_isUnramifiedAt_int (K := K) (𝒪 := 𝓞 K) h.ne'
  refine ⟨absNorm (Ideal.under ℤ 𝔮), Nat.absNorm_under_prime 𝔮, 𝔮, hq, Int.liesOver_span_absNorm 𝔮, ?_⟩
  rwa [Int.ideal_span_absNorm_eq_self, ← Algebra.not_isUnramifiedAt_iff_of_isDedekindDomain]
  exact IsMaximal.ne_bot_of_isIntegral_int 𝔮

/-- **Tame Abhyankar (ramification index, hard direction).** For a Galois `K/ℚ`, two Galois
intermediate fields `E`, `F` with `E ⊔ F = ⊤`, and a prime `𝔓` of `𝓞 K` over a rational prime `p`
tame in `K` (`p ∤ [K:ℚ]`), the ramification index `e(𝔓 ∣ p)` divides the lcm of the ramification
indices of the primes below `𝔓` in `E` and `F`. (The easy direction `lcm ∣ e(𝔓 ∣ p)` is just the
ramification tower.) -/
theorem ramificationIdx_sup_dvd_lcm {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (E F : IntermediateField ℚ K) [IsGalois ℚ E] [IsGalois ℚ F] (hEF : E ⊔ F = ⊤) {p : ℕ}
    (htame : ¬ p ∣ Module.finrank ℚ K) (𝔓 : Ideal (𝓞 K)) [𝔓.IsMaximal]
    [hPp : 𝔓.LiesOver (span {(p : ℤ)})] :
    𝔓.ramificationIdx ℤ ∣
      Nat.lcm ((under (𝓞 E) 𝔓).ramificationIdx ℤ) ((under (𝓞 F) 𝔓).ramificationIdx ℤ) := by
  let 𝔭 : Ideal ℤ := span {(p : ℤ)}
  have : 𝔭.IsPrime := isPrime_of_liesOver 𝔓 𝔭
  have : IsCyclic (inertia Gal(K/ℚ) 𝔓) := by
    have : FaithfulSMul Gal(K/ℚ) (𝓞 K) := IsGaloisGroup.faithful ℤ
    have : ↑(Nat.card (inertia Gal(K/ℚ) 𝔓)) ∉ 𝔓 := by
      apply card_inertia_notMem_of_not_dvd
      simpa [← (liesOver_iff _ _).mp hPp, - Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact isCyclic_inertia' 𝔓 this
  let I := 𝔓.inertia Gal(K/ℚ)
  have := card_dvd_lcm_of_isCyclic_of_inf_eq_bot (G := I)
    (H₁ := (I ⊓ E.fixingSubgroup).subgroupOf I) (H₂ := (I ⊓ F.fixingSubgroup).subgroupOf I) ?_
  · convert this
    · rw [card_inertia_eq_ramificationIdxIn 𝔭, ramificationIdxIn_eq_ramificationIdx 𝔭 𝔓 Gal(K/ℚ)]
    · rw [eq_comm, Subgroup.index_eq_iff_card_mul_eq_card, Subgroup.inf_subgroupOf_left,
        ← ramificationIdxIn_eq_ramificationIdx 𝔭 _ Gal(E/ℚ)]
      have hmain := ramificationIdxIn_mul_ramificationIdxIn (A := ℤ) (p := 𝔭) (under (𝓞 E) 𝔓)
        Gal(E/ℚ) (𝓞 K) Gal(K/ℚ) E.fixingSubgroup
      rwa [← card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) 𝔭 𝔓,
        ← card_inertia_eq_ramificationIdxIn (G := E.fixingSubgroup) (under (𝓞 E) 𝔓) 𝔓,
        mul_comm, ← Ideal.subgroupOf_inertia,
        Nat.card_congr (Subgroup.subgroupOfEquivComm _ _).toEquiv] at hmain
    · rw [eq_comm, Subgroup.index_eq_iff_card_mul_eq_card, Subgroup.inf_subgroupOf_left,
        ← ramificationIdxIn_eq_ramificationIdx 𝔭 _ Gal(F/ℚ)]
      have hmain := ramificationIdxIn_mul_ramificationIdxIn (A := ℤ) (p := 𝔭) (under (𝓞 F) 𝔓)
        Gal(F/ℚ) (𝓞 K) Gal(K/ℚ) F.fixingSubgroup
      rwa [← card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) 𝔭 𝔓,
        ← card_inertia_eq_ramificationIdxIn (G := F.fixingSubgroup) (under (𝓞 F) 𝔓) 𝔓,
        mul_comm, ← Ideal.subgroupOf_inertia,
        Nat.card_congr (Subgroup.subgroupOfEquivComm _ _).toEquiv] at hmain
  · rw [Subgroup.inf_subgroupOf_left, Subgroup.inf_subgroupOf_left, ← Subgroup.subgroupOf_inf,
      ← fixingSubgroup_sup, hEF, fixingSubgroup_top, Subgroup.bot_subgroupOf]

set_option synthInstance.maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
/-- Ramification reduction: given `K/ℚ` cyclic of prime power degree `pᵐ` with `q ≠ p` ramified,
there is a cyclic `F/ℚ` of degree `pᵐ` (in the same ambient field `A`), unramified at `q` and not
ramified at any prime where `K` is unramified, such that `K · ℚ(ζ_q) = F · ℚ(ζ_q)`. This removes `q`
from the set of ramified primes at the cost of the `q`-th cyclotomic factor. (`ℚ(ζ_q)` already
suffices, since for the abelian `K` the tame inertia order at `q` divides `q - 1`.) -/
lemma kw_ramification_reduction {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] (m : ℕ) (hK : Module.finrank ℚ K = p ^ m) (q : ℕ)
    (hq : q.Prime) (hqp : q ≠ p) (hram : ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F),
      IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ (∃ k, Module.finrank ℚ F = p ^ k) ∧
      Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)}) ∧
      (∀ q' : ℕ, q'.Prime → Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q' : ℤ)}) →
        Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q' : ℤ)})) ∧ K ⊔ ℚ⟮ξ q⟯ = F ⊔ ℚ⟮ξ q⟯ := by
  let E := ℚ⟮ξ q⟯
  let L := K ⊔ E
  let 𝔮 : Ideal ℤ := span {(q : ℤ)}
  have : Fact q.Prime := sorry
  have : 𝔮.IsPrime := sorry
  have : NumberField L := sorry
  have : IsAbelianGalois ℚ L := sorry
  let G := Gal(L/ℚ)
  have : FaithfulSMul G (𝓞 L) := IsGaloisGroup.faithful ℤ
  have hF : finrank ℚ L ∣ p ^ m * (q - 1) := sorry
  have hq₁ : ¬ q ∣ finrank ℚ L := sorry
  obtain ⟨𝔔, _, h𝔔⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral 𝔮 (S := 𝓞 L)
  have h₁ : IsCyclic (Ideal.inertia G 𝔔) ∧
      Nat.card (Ideal.inertia G 𝔔) = ramificationIdx 𝔔 ℤ := by
    refine ⟨?_, ?_⟩
    · have : ↑(Nat.card (inertia G 𝔔)) ∉ 𝔔 := sorry
      exact isCyclic_inertia' 𝔔 this
    · rw [card_inertia_eq_ramificationIdxIn 𝔮 𝔔, ramificationIdxIn_eq_ramificationIdx 𝔮 𝔔 G]
  let E' : IntermediateField ℚ L := E.restrict le_sup_right
  have : IsCyclotomicExtension {q} ℚ E' := sorry
  have : IsGalois ℚ E' := sorry
  have h₂ : 𝔔.ramificationIdx ℤ = q - 1 := by
    apply dvd_antisymm
    · let K' : IntermediateField ℚ L := K.restrict le_sup_left
      have : IsAbelianGalois ℚ K' := sorry
      have hK' : finrank ℚ K' = p ^ m := sorry
      have : FaithfulSMul Gal(K'/ℚ) (𝓞 K') := IsGaloisGroup.faithful ℤ
      have : IsGalois ℚ E' := sorry
      have := ramificationIdx_sup_dvd_lcm K' E' ?_ ?_ 𝔔 (p := q)
      refine dvd_trans this <| Nat.lcm_dvd ?_ ?_
      · rw [← ramificationIdxIn_eq_ramificationIdx 𝔮 _ Gal(K'/ℚ),
          ← card_inertia_eq_ramificationIdxIn 𝔮 (under (𝓞 K') 𝔔) (G := Gal(K'/ℚ))]
        convert card_inertia_dvd_card_sub_one' (G := Gal(K'/ℚ)) (under (𝓞 K') 𝔔) (R := ℤ) ?_
        · have : (under (𝓞 K') 𝔔).LiesOver 𝔮 := sorry
          simp [← (liesOver_iff _ _).mp this, 𝔮, Int.card_ideal_quot]
        · apply card_inertia_notMem_of_not_dvd
          simp [- Nat.card_eq_fintype_card, ← (liesOver_iff _ _).mp h𝔔,
            IsGalois.card_aut_eq_finrank, 𝔮, hK']
          exact fun h ↦ hqp <| (Nat.prime_dvd_prime_iff_eq hq hp.out).mp <| hq.dvd_of_dvd_pow h
      · rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime q]
      · exact lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_top])
      exact hq₁
    · have : IsCyclotomicExtension {q} ℚ E' := sorry
      rw [ramificationIdx_tower (R := ℤ) (under (𝓞 E') 𝔔),
        IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime q E']
      exact dvd_mul_right (q - 1) _
  have h₃ : 𝔔.ramificationIdx (𝓞 E') = 1 := by
    have := ramificationIdx_tower (R := ℤ) (under (𝓞 E') 𝔔) 𝔔
    rwa [h₂, IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime q E',
      left_eq_mul₀ (by grind [hq.one_lt])] at this
  have h₄ : 𝔔.inertia G ⊓ E'.fixingSubgroup = ⊥ := by
    rw [Subgroup.eq_bot_iff_card, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype,
      Ideal.subgroupOf_inertia, card_inertia_eq_ramificationIdxIn (under (𝓞 E') 𝔔) 𝔔,
      ramificationIdxIn_eq_ramificationIdx (under (𝓞 E') 𝔔) 𝔔 E'.fixingSubgroup]
    exact h₃
  have h₅ : Subgroup.IsComplement' (𝔔.inertia G) E'.fixingSubgroup := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ (disjoint_iff.mpr <| h₄)
    rw [IsGalois.card_aut_eq_finrank, ← finrank_mul_finrank ℚ E', h₁.2, h₂,
      IsGalois.card_fixingSubgroup_eq_finrank,
      IsCyclotomicExtension.Rat.finrank q E', Nat.totient_prime hq]
  let F : IntermediateField ℚ L := fixedField (inertia G 𝔔)
  have hF : IsGaloisGroup (inertia G 𝔔) F L := .of_fixedPoints_eq G ℚ L (inertia G 𝔔) _ rfl
  refine ⟨lift (fixedField (𝔔.inertia G)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · have : IsCyclic Gal(fixedField (inertia G 𝔔)/ℚ) := sorry
    infer_instance
  ·
    sorry
  · have : IsInertiaField ℚ L 𝔔 (fixedField (inertia G 𝔔)) := (isInertiaField_iff ℚ _ 𝔔 _).mpr hF

    sorry
  ·
    sorry
  ·
    sorry


  -- ROUTE (a): inertia / fixed field.  Write `E = ℚ(ζ_q) = ℚ⟮ξ q⟯`, `L = K ⊔ E`, `G = Gal(L/ℚ)`.
  -- `F` will be the **inertia field** of a prime `𝔔 ∣ q` of `𝓞 L` (the fixed field of its inertia
  -- group), lifted back into `A`.
  --
  -- Preliminaries.
  --   • `E` is cyclotomic (`hξ q : IsPrimitiveRoot (ξ q) q`): `NumberField E`, `IsGalois ℚ E`,
  --     `IsCyclic Gal(E/ℚ) ≅ (ℤ/q)ˣ`, and `E` is **totally ramified** at `q` with `e(E) = q - 1`.
  --   • `L = K·E` is a `NumberField`, `IsGalois ℚ L`, and `G := Gal(L/ℚ)` is **abelian** (compositum
  --     of the abelian `K` and `E`).  Restriction gives `G ↪ Gal(K/ℚ) × Gal(E/ℚ)`, injective because
  --     `L = K·E`, i.e. `Gal(L/K) ⊓ Gal(L/E) = ⊥`.
  --
  -- Step 1 (tame inertia).  Fix a prime `𝔔 ∣ q` of `𝓞 L` and set `I := Ideal.inertia G 𝔔 ⊆ G`.
  --   Since `q ≠ p` and `q ∤ [L:ℚ]` (because `[L:ℚ] ∣ pᵐ·(q-1)`, coprime to `q`), `q` is tame, so:
  --     · `I` is cyclic (`isCyclic_inertia'`, the full-`G` form);
  --     · `Nat.card I = e(𝔔 ∣ q) = e(L)` (Mathlib `card_inertia_eq_ramificationIdxIn`, bridged to
  --       `𝔔.ramificationIdx ℤ` via `ramificationIdxIn_eq_ramificationIdx`).
  --
  -- Step 2 (Abhyankar: `q` unramified in `L/E`).  Viewing `K`, `E` as intermediate fields of `L`
  --   (`K ⊔ E = ⊤` in `L`), `ramificationIdx_sup_dvd_lcm` applied to `𝔔` gives
  --   `e(L) ∣ Nat.lcm (e K) (e E)` directly -- this stays inside `G ↷ 𝓞 L` (index form, via
  --   `coe_mem_inertia` + tower), so NO cross-ring inertia functoriality is needed.  Now `e K = p^a`
  --   and `card_inertia_dvd_card_sub_one'` gives `p^a ∣ q - 1 = e E`, so `lcm (e K) (e E) = q - 1`;
  --   with `e E ∣ e L` (tower `E ⊆ L`, `ramificationIdx_tower`) we conclude `e L = q - 1 = e E`.
  --   Hence `e(L/E) = e L / e E = 1`, i.e. **`I ⊓ Gal(L/E) = ⊥`** (`q` unramified in `L/E`).
  --
  -- Step 3 (direct product).  `G` abelian, `I ⊓ Gal(L/E) = ⊥`, and
  --   `Nat.card I · Nat.card Gal(L/E) = (q-1)·[L:E] = [L:ℚ] = Nat.card G`, so **`G = I × Gal(L/E)`**.
  --
  -- Step 4 (the field `F`).  Let `F := IntermediateField.lift (fixedField I)` (inertia field of `𝔔`).
  --     • **`F` unramified at `q`**: `Gal(L/F) = I` is the inertia, so `F` is the inertia field
  --       (ramification index `1` at `q`).
  --     • **`F` cyclic** and **`p`-power degree**: `Gal(F/ℚ) ≅ G/I ≅ Gal(L/E) ≅ Gal(K / K∩E)`, a
  --       subgroup of the cyclic `Gal(K/ℚ)`; and `[F:ℚ] = [G:I] = [L:E] = [K:K∩E] ∣ pᵐ`.
  --     • **`K ⊔ ℚ⟮ξ q⟯ = F ⊔ ℚ⟮ξ q⟯`**: `F ⊔ E ↔ I ⊓ Gal(L/E) = ⊥ ↔ L = K ⊔ E` (Galois corresp.).
  --     • **no new ramified prime**: `F ⊆ L`, `L` ramifies only where `K` or `E` do, `E` only at `q`,
  --       and `F` is unramified at `q`; so `K` unramified at `q' ⟹ F` unramified at `q'`.
  --
  -- Assemble `⟨F, ‹NumberField F›, ‹IsGalois ℚ F›, ‹IsCyclic Gal(F/ℚ)›, ⟨k, hk⟩, hFq, hFpres, hcomp⟩`.
  --
  -- Sub-lemmas to discharge:
  --   (i)   instances `NumberField L`, `IsGalois ℚ L`, `IsMulCommutative Gal(L/ℚ)`;
  --   (ii)  `E` totally ramified at `q`, `e E = q - 1`;
  --   (iii) view `K`, `E` as `IntermediateField ℚ L` with `K ⊔ E = ⊤`, matching `ramificationIdx`
  --         across the `A`- and `L`-currencies (same rings of integers), to apply
  --         `ramificationIdx_sup_dvd_lcm` -- routine bookkeeping, NOT inertia functoriality;
  --   (iv)  `Nat.card I = e L` (`card_inertia_eq_ramificationIdxIn`, bridged) and the tower
  --         `e L = e(L/E) · e E` (`ramificationIdx_tower`);
  --   (v)   `G = I × Gal(L/E)`; for `F = fixedField I`: degree, cyclicity, `F ⊔ E = L`, unramified at `q`.


/-- Auxiliary form of `kw_reduce_to_unramified_outside_p`, generalized over a finite set `S` of
primes (assumed to contain every `q ≠ p` ramified in `K`) and over `K`. Proved by induction on `S`,
peeling one ramified prime at a time with `kw_ramification_reduction`. -/
lemma kw_reduce_to_unramified_outside_p_aux {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A)
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (S : Finset ℕ)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (hK : ∃ k, Module.finrank ℚ K = p ^ k)
    (hram : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ S → Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})) :
      ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (_ : IsGalois ℚ F) (_ : IsCyclic Gal(F/ℚ)),
        (∃ k, Module.finrank ℚ F = p ^ k) ∧
        (∀ q : ℕ, q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)})) ∧
        ∃ n, 0 < n ∧ K ⊔ ℚ⟮ξ n⟯ = F ⊔ ℚ⟮ξ n⟯ := by
  induction S using Finset.induction generalizing K with
  | empty => exact ⟨K, ‹_›, ‹_›, ‹_›, hK, by simpa using hram, 1, Nat.one_pos, rfl⟩
  | insert r S' hq ih =>
      by_cases hr₁ : r.Prime ∧ r ≠ p
      · by_cases hr₂ : Algebra.IsUnramifiedIn (𝓞 K) (span {(r : ℤ)})
        · refine ih K hK fun q hq₁ hq₂ hq₃ ↦ ?_
          by_cases hq : q = r
          · rwa [hq]
          · exact hram q hq₁ hq₂ (by grind)
        · obtain ⟨k, hk⟩ := hK
          obtain ⟨E, _, _, _, hE₁, hE₂, hE₃, hE₄⟩ :=
            kw_ramification_reduction hξ K k hk r hr₁.1 hr₁.2 hr₂
          have hunram (q : ℕ) (hq : Nat.Prime q) (hqp : q ≠ p)(hqS' :q ∉ S') :
              Algebra.IsUnramifiedIn (𝓞 E) (span {(q : ℤ)}) := by
            by_cases hqr : q = r
            · rwa [hqr]
            · exact hE₃ q hq (hram q hq hqp (by grind))
          obtain ⟨F, _, _, _, hF₁, hF₂, n, hn, hF₃⟩ := ih E hE₁ hunram
          have : NeZero n := NeZero.of_gt hn
          have : Fact r.Prime := ⟨hr₁.1⟩
          have : NeZero (n.lcm r) := ⟨Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
          refine ⟨F, ‹_›, ‹_›, ‹_›, hF₁, fun q hq hqp ↦  hF₂ q hq hqp, n.lcm r, NeZero.pos _, ?_⟩
          have : ℚ⟮ξ (n.lcm r)⟯ = ℚ⟮ξ n⟯ ⊔ ℚ⟮ξ r⟯ := by
            have := (hξ n).adjoinSimple_isCyclotomicExtension n ℚ A
            have := (hξ r).adjoinSimple_isCyclotomicExtension r ℚ A
            have := isCyclotomicExtension_lcm_sup ℚ A n r ℚ⟮ξ n⟯ ℚ⟮ξ r⟯
            have := (hξ (n.lcm r)).adjoinSimple_isCyclotomicExtension (n.lcm r) ℚ A
            exact IntermediateField.isCyclotomicExtension_eq {n.lcm r} ℚ A _ _
          rw [this, ← sup_assoc, sup_right_comm, hE₄, sup_right_comm, hF₃, sup_assoc]
      · refine ih K hK fun q hq₁ hq₂ hq₃ ↦ hram _ hq₁ hq₂ ?_
        rw [Finset.mem_insert, not_or]
        exact ⟨by grind, hq₃⟩

/-- Consumer of `kw_ramification_reduction`: iterating it over the finitely many primes `q ≠ p`
ramified in `K`, one obtains a cyclic `F/ℚ` of the same prime power degree, unramified outside `p`,
with `K ⊔ ℚ⟮ξ n⟯ = F ⊔ ℚ⟮ξ n⟯` for some `n` (so `K` is cyclotomic iff `F` is). The "unramified
outside `p`" condition is spelled out inline as `∀ q ≠ p prime, Algebra.IsUnramifiedIn (𝓞 F) (q)`. -/
lemma kw_reduce_to_unramified_outside_p {A : Type*} [Field A] [CharZero A] (ξ : ℕ → A)
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] (m : ℕ) (hK : Module.finrank ℚ K = p ^ m) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (_ : IsGalois ℚ F) (_ : IsCyclic Gal(F/ℚ)),
      (∃ k, Module.finrank ℚ F = p ^ k) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)})) ∧
      ∃ n, 0 < n ∧ K ⊔ ℚ⟮ξ n⟯ = F ⊔ ℚ⟮ξ n⟯ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ≠ p → q ∉ S →
      Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)}) := by
    refine ⟨(discr K).natAbs.primeFactors, fun q hq hpq hD ↦ ?_⟩
    refine (not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hq)).mp ?_
    contrapose! hD
    exact hq.mem_primeFactors (by rwa [← Int.natCast_dvd])
      (Int.natAbs_ne_zero.mpr <| discr_ne_zero K)
  exact kw_reduce_to_unramified_outside_p_aux ξ hξ S K ⟨m, hK⟩ hS

set_option backward.isDefEq.respectTransparency false in
/-- Two cyclic `p`-extensions `K`, `K'` of `ℚ` inside a common ambient `A`, whose compositum
`K ⊔ K'` is cyclic over `ℚ`, are comparable (`K ≤ K'`) once `[K:ℚ] ∣ [K':ℚ]`. -/
lemma kw_cyclic_compositum {A : Type*} [Field A] [CharZero A] (K K' : IntermediateField ℚ A)
    [NumberField ↑(K ⊔ K')] [IsGalois ℚ ↑(K ⊔ K')] [IsCyclic Gal(↑(K ⊔ K')/ℚ)]
    (h : Module.finrank ℚ K ∣ Module.finrank ℚ K') : K ≤ K' := by
  rw [← restrict_le_restrict_iff (le_sup_left : K ≤ K ⊔ K') (le_sup_right : K' ≤ K ⊔ K')]
  set J := K.restrict (le_sup_left : K ≤ K ⊔ K')
  set J' := K'.restrict (le_sup_right : K' ≤ K ⊔ K')
  replace h : finrank ℚ J ∣ finrank ℚ J' := by
    rw [finrank_restrict, finrank_restrict]; exact h
  rw [← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(↑(K ⊔ K')/ℚ) ℚ ↑(K ⊔ K') J,
    ← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(↑(K ⊔ K')/ℚ) ℚ ↑(K ⊔ K') J']
  apply IsGaloisGroup.fixedPoints_le_of_le
  rw [IsCyclic.subgroup_le_subgroup_iff, IsGaloisGroup.card_fixingSubgroup_eq_finrank,
    IsGaloisGroup.card_fixingSubgroup_eq_finrank]
  have hd : finrank ℚ J ∣ finrank ℚ ↑(K ⊔ K') :=
    finrank_mul_finrank ℚ J ↑(K ⊔ K') ▸ dvd_mul_right _ _
  have hd' : finrank ℚ J' ∣ finrank ℚ ↑(K ⊔ K') :=
    finrank_mul_finrank ℚ J' ↑(K ⊔ K') ▸ dvd_mul_right _ _
  have he : finrank J ↑(K ⊔ K') = finrank ℚ ↑(K ⊔ K') / finrank ℚ J :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  have he' : finrank J' ↑(K ⊔ K') = finrank ℚ ↑(K ⊔ K') / finrank ℚ J' :=
    Nat.eq_div_of_mul_eq_right finrank_pos.ne' (by rw [finrank_mul_finrank])
  rwa [he, he', Nat.div_dvd_div_iff finrank_pos finrank_pos hd' hd]

end

end
