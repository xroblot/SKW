module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.ClassGroup.Basic

set_option linter.style.header false

public section

/-!
# Prerequisites for Stickelberger's theorem

This file gathers the results from the `SKW.Prereqs` files that are needed in
`SKW.Stickelberger.Stickelberger`.
-/

open NumberField

theorem NumberField.isUnit_iff_natAbs_norm {K : Type*} [Field K] [NumberField K] {x :
  RingOfIntegers K} :
    IsUnit x ↔ (Algebra.norm ℤ x).natAbs = 1 := by
  rw [isUnit_iff_norm, ← Rat.natCast_injective.eq_iff, RingOfIntegers.coe_norm,
    Nat.cast_natAbs, Nat.cast_one, ← Algebra.coe_norm_int, Int.cast_abs]

-- TODO(SKW): upstream, next to `ZMod.ringHom_map_cast` in `Mathlib/Data/ZMod/Basic.lean`, which
-- is the statement for a ring homomorphism into `ZMod n`, probably with `@[simp]` like it.
/-- A ring homomorphism commutes with the cast from `ZMod n`. -/
theorem ZMod.map_cast {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (k : ZMod n) :
    f (ZMod.cast k) = ZMod.cast k := by
  cases n
  · exact map_intCast f k
  · exact map_natCast f k.val

-- TODO(SKW): no obvious home in Mathlib, `Mathlib/RingTheory/Trace/Basic.lean`, next to
-- `Algebra.trace_eq_of_equiv_equiv`, knowing nothing about `ZMod`.
/-- The trace does not care whether the base ring is `ZMod p` or a ring isomorphic to it. -/
theorem ZMod.cast_trace_eq_trace {p : ℕ} {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [Algebra (ZMod p) C] (e : A ≃+* ZMod p) (x : C) :
    ZMod.cast (Algebra.trace (ZMod p) C x) = Algebra.trace A C x := by
  have : Subsingleton (A →+* C) := ⟨fun f g ↦ RingHom.ext fun y ↦ by
    obtain ⟨z, rfl⟩ := e.symm.surjective y
    exact congr($(Subsingleton.elim (f.comp (e.symm : ZMod p →+* A)) (g.comp e.symm)) z)⟩
  rw [Algebra.trace_eq_of_equiv_equiv e (RingEquiv.refl C) (Subsingleton.elim _ _) x]
  exact e.eq_symm_apply.mpr (ZMod.ringHom_map_cast (e : A →+* ZMod p) _)

-- TODO(SKW): upstream, next to `Nat.pow_sub_one_mod_pow_sub_one` in
-- `Mathlib/Data/Nat/GCD/Basic.lean`.
/-- For `1 < a`, the number `a ^ m - 1` divides `a ^ n - 1` precisely when `m` divides `n`. -/
theorem Nat.pow_sub_one_dvd_pow_sub_one_iff {a : ℕ} (ha : 1 < a) {n m : ℕ} :
    a ^ m - 1 ∣ a ^ n - 1 ↔ m ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.pow_sub_one_mod_pow_sub_one, Nat.sub_eq_zero_iff_le,
    ← pow_zero a, Nat.pow_le_pow_iff_right ha, Nat.le_zero, Nat.dvd_iff_mod_eq_zero]

theorem ZMod.orderOf_pow_sub_one (a k : ℕ) (ha : 1 < a) :
    orderOf (a : ZMod (a ^ k - 1)) = k := by
  have key (n : ℕ) : (a : ZMod (a ^ k - 1)) ^ n = 1 ↔ k ∣ n := by
    rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod (a ^ k - 1)), ZMod.natCast_eq_natCast_iff,
      Nat.ModEq.comm, Nat.modEq_iff_dvd, ← Nat.cast_sub (Nat.one_le_pow _ _ (by lia : 0 < a)),
      Int.natCast_dvd_natCast, Nat.pow_sub_one_dvd_pow_sub_one_iff ha]
  exact Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr ((key k).mpr dvd_rfl))
    ((key _).mp (pow_orderOf_eq_one _))

theorem smul_eq_galRestrict_apply (A : Type*) {K L B : Type*} [CommRing A] [Field K] [Field L]
    [CommRing B] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] (σ : Gal(L/K)) (x : B) :
    σ • x = galRestrict A K L B σ x := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [algebraMap.smul', AlgEquiv.smul_def, algebraMap_galRestrict_apply]

open NumberField in
theorem IsCyclotomicExtension.Rat.isCoprime_discr_of_coprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (K₁ K₂ : Type*) [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [IsCyclotomicExtension {n₁} ℚ K₁] [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
  rw [Int.isCoprime_iff_nat_coprime, natAbs_discr  n₁ K₁, natAbs_discr  n₂ K₂]
  refine Nat.Coprime.coprime_div_left ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
  refine Nat.Coprime.coprime_div_right ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos
    _))
  exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ h)

theorem IntermediateField.linearDisjoint_iff_linearDisjoint_fieldRange {F E : Type*} [Field F]
    [Field E] [Algebra F E] (A : IntermediateField F E) (L : Type*) [Field L] [Algebra F L]
    [Algebra L E] [IsScalarTower F L E] :
    A.LinearDisjoint L ↔ A.LinearDisjoint (IsScalarTower.toAlgHom F L E).fieldRange := by
  rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]

theorem IsCyclotomicExtension.Rat.linearDisjoint_of_coprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    {E : Type*} [Field E] [NumberField E] (K₁ : IntermediateField ℚ E) [NumberField K₁] (K₂ : Type*)
    [Field K₂] [NumberField K₂] [Algebra K₂ E] [IsCyclotomicExtension {n₁} ℚ K₁]
    [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    K₁.LinearDisjoint K₂ := by
  have : IsCyclotomicExtension {n₂} ℚ (IsScalarTower.toAlgHom ℚ K₂ E).fieldRange :=
    .equiv _ ℚ K₂ (IsScalarTower.toAlgHom ℚ K₂ E).equivFieldRange
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois {n₁} ℚ K₁
  rw [IntermediateField.linearDisjoint_iff_linearDisjoint_fieldRange]
  exact NumberField.linearDisjoint_of_isGalois_isCoprime_discr E _ _ <|
    isCoprime_discr_of_coprime n₁ n₂ K₁ _ h

open Module in
lemma IntermediateField.finrank_sup_eq_of_inf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional F K] [FiniteDimensional F L]
    [Algebra K ↑(K ⊔ L)] [IsScalarTower F K ↑(K ⊔ L)] (hinf : K ⊓ L = ⊥) :
    finrank K ↑(K ⊔ L) = finrank F L := by
  rw [← mul_right_inj', ← (LinearDisjoint.of_inf_eq_bot hinf).finrank_sup, finrank_mul_finrank]
  exact finrank_pos.ne'

set_option maxHeartbeats 500000 in
-- reason for change
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
open Module in
theorem IntermediateField.finrank_sup_mul_finrank_inf_eq {k L : Type*} [Field k] [Field L] [Algebra
  k L]
    (E F : IntermediateField k L) [FiniteDimensional k E] [FiniteDimensional k F] [IsGalois k E] :
    finrank k ↑(E ⊔ F) * finrank k ↑(E ⊓ F) = finrank k E * finrank k F := by
  let : Algebra E ↑(E ⊔ F) := (inclusion le_sup_left).toRingHom.toAlgebra
  have : FiniteDimensional k ↑(E ⊓ F) := FiniteDimensional.of_injective
    (IntermediateField.inclusion inf_le_left).toLinearMap
    (RingHom.injective _)
  suffices h : finrank E ↑(E ⊔ F) = finrank ↑(E ⊓ F) F by
    rwa [← finrank_mul_finrank k E ↑(E ⊔ F), ← finrank_mul_finrank k ↑(E ⊓ F) F, mul_assoc,
      mul_right_inj' finrank_pos.ne', mul_comm, mul_right_inj' finrank_pos.ne']
  let : Algebra ↑(E ⊓ F) ↑(E ⊔ F) := (inclusion inf_le_sup).toRingHom.toAlgebra
  have : IsScalarTower ↑(E ⊓ F) E ↑(E ⊔ F) := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional ↑(E ⊓ F) E := FiniteDimensional.right k _ _
  have : FiniteDimensional ↑(E ⊓ F) F := FiniteDimensional.right k _ _
  have : finrank ↑(E ⊓ F) E ≠ 0 := finrank_pos.ne'
  rw [← mul_right_inj' this, finrank_mul_finrank]
  let E' : IntermediateField ↑(E ⊓ F) L := E.extendScalars (F := E ⊓ F) inf_le_left
  let F' : IntermediateField ↑(E ⊓ F) L := F.extendScalars (F := E ⊓ F) inf_le_right
  let : Algebra E' ↑(E' ⊔ F') := (inclusion le_sup_left).toRingHom.toAlgebra
  let e' : E ≃ₐ[↑(E ⊓ F)] E' := AlgEquiv.refl
  let f' : F ≃ₐ[↑(E ⊓ F)] F' := AlgEquiv.refl
  let h : ↑(E' ⊔ F') ≃ₗ[↑(E ⊓ F)] ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup) :=
    LinearEquiv.ofEq ↑(E' ⊔ F').toSubalgebra.toSubmodule
      ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup).toSubalgebra.toSubmodule
        (by simpa using (extendScalars_sup (F := E ⊓ F) inf_le_left inf_le_right))
  have : IsGalois ↑(E ⊓ F) E' := by
    have : IsGalois ↑(E ⊓ F) E := IsGalois.tower_top_of_isGalois k _ _
    exact IsGalois.of_algEquiv e'
  have : FiniteDimensional ↑(E ⊓ F) E' := Module.Finite.equiv e'.toLinearEquiv
  have : FiniteDimensional ↑(E ⊓ F) F' := Module.Finite.equiv f'.toLinearEquiv
  calc finrank ↑(E ⊓ F) ↑(E ⊔ F)
      = finrank ↑(E ⊓ F) ↑(E' ⊔ F') := ?_
    _ = finrank ↑(E ⊓ F) E' * finrank E' ↑(E' ⊔ F') := by rw [finrank_mul_finrank]
    _ = finrank ↑(E ⊓ F) E * finrank E' ↑(E' ⊔ F') := by rw [e'.toLinearEquiv.finrank_eq]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F' := by
        rw [← finrank_sup_eq_of_inf_eq_bot E' F']
        ext; simp [E', F', mem_bot]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F := by rw [f'.toLinearEquiv.finrank_eq]
  · rw [LinearEquiv.finrank_eq (M := ↑(E ⊔ F)) (N := ↑(E' ⊔ F'))]
    exact (LinearEquiv.refl ↑(E ⊓ F) ↑(E ⊔ F)).trans h.symm

@[expose] def ArithmeticFunction.totient : ArithmeticFunction ℤ where
  toFun n := Nat.totient n
  map_zero' := by simp

@[simp]
theorem ArithmeticFunction.totient_apply (n : ℕ) :
    totient n = Nat.totient n := rfl

open Nat in
theorem ArithmeticFunction.isMultiplicative_totient :
    IsMultiplicative totient :=
  IsMultiplicative.iff_ne_zero.mpr ⟨by simp, fun _ _ h ↦ by simp [Nat.totient_mul h]⟩

theorem Nat.totient_lcm_mul_totient_gcd (m n : ℕ) :
    totient (lcm m n) * totient (gcd m n) = totient m * totient n := by
  have :=  ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply
    ArithmeticFunction.isMultiplicative_totient (x := m) (y := n)
  rwa [ArithmeticFunction.totient_apply, ArithmeticFunction.totient_apply,
    ArithmeticFunction.totient_apply, ArithmeticFunction.totient_apply, ← Nat.cast_mul,
    ← Nat.cast_mul, Nat.cast_inj] at this

open IntermediateField in
set_option backward.isDefEq.respectTransparency false in
theorem IsCyclotomicExtension.Rat.gcd_inf {K : Type*} [Field K] [NumberField K]
    (n₁ n₂ : ℕ) (F₁ F₂ : IntermediateField ℚ K) [h₁ : IsCyclotomicExtension {n₁} ℚ F₁]
    [h₂ : IsCyclotomicExtension {n₂} ℚ F₂] [NeZero n₁] [NeZero n₂] :
    IsCyclotomicExtension {n₁.gcd n₂} ℚ ↑(F₁ ⊓ F₂) := by
  let d := n₁.gcd n₂
  have : NeZero d := ⟨Nat.gcd_ne_zero_left (NeZero.ne _)⟩
  have : NeZero (n₁.lcm n₂) := ⟨Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨ζ₁, hζ₁⟩ := h₁.1 rfl (NeZero.ne n₁)
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective F₁ K)
  obtain ⟨s, hs⟩ := n₁.gcd_dvd_left n₂
  let ζ := (algebraMap F₁ K ζ₁) ^ s
  have hζ : IsPrimitiveRoot ζ d := hζ₁.pow (NeZero.pos n₁) (by rwa [mul_comm])
  have : IsCyclotomicExtension {d} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  rw [isCyclotomicExtension_singleton_iff_eq_adjoin d ℚ K _ hζ, eq_comm]
  rw [eq_iff_finrank_eq_of_le]
  · have : IsGalois ℚ F₁ := h₁.isGalois
    have := isCyclotomicExtension_lcm_sup ℚ K n₁ n₂ F₁ F₂
    have : Module.finrank ℚ ↑(F₁ ⊔ F₂) ≠ 0 := Module.finrank_pos.ne'
    rw [← mul_right_inj' this, finrank_sup_mul_finrank_inf_eq,
      IsCyclotomicExtension.Rat.finrank n₁ F₁,
      IsCyclotomicExtension.Rat.finrank n₂ F₂,
        IsCyclotomicExtension.Rat.finrank (n₁.lcm n₂) ↑(F₁ ⊔ F₂),
      IsCyclotomicExtension.Rat.finrank d ℚ⟮ζ⟯, Nat.totient_lcm_mul_totient_gcd]
  · obtain ⟨ζ₂, hζ₂⟩ := h₂.1 rfl (NeZero.ne n₂)
    replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective F₂ K)
    rw [(isCyclotomicExtension_singleton_iff_eq_adjoin n₁ ℚ K _ hζ₁).mp h₁,
      (isCyclotomicExtension_singleton_iff_eq_adjoin n₂ ℚ K _ hζ₂).mp h₂, adjoin_simple_le_iff,
        mem_inf]
    constructor
    · exact pow_mem (mem_adjoin_simple_self ℚ _) s
    · obtain ⟨t, _,
      ht⟩ := hζ₂.eq_pow_of_pow_eq_one <| (hζ.pow_eq_one_iff_dvd n₂).mpr (n₁.gcd_dvd_right n₂)
      rw [← ht]
      exact pow_mem (mem_adjoin_simple_self ℚ _) t

/-- `restrictHom` is `AlgEquiv.restrictNormal`. -/
theorem IsGaloisGroup.restrictHom_eq_restrictNormal (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional K L]
    [FiniteDimensional K E] [IsGalois K L] [IsGalois K E] (σ : Gal(L/K)) :
    IsGaloisGroup.restrictHom Gal(L/K) Gal(E/K) K E L σ = σ.restrictNormal E := by
  ext x
  apply (algebraMap E L).injective
  rw [← AlgEquiv.smul_def, IsGaloisGroup.algebraMap_restrictHom_smul, AlgEquiv.smul_def,
    AlgEquiv.restrictNormal_commutes]

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

/-- `restrictHom` does not depend on the tower `C/B/A` used to define it, as long as the
actions of `G` and `G'` are compatible with the maps `B → B'` and `C → C'`. -/
theorem IsGaloisGroup.restrictHom_eq_restrictHom :
    IsGaloisGroup.restrictHom G G' A B C = IsGaloisGroup.restrictHom G G' A' B' C' := by
  ext g
  have : FaithfulSMul G' B := IsGaloisGroup.faithful A
  refine eq_of_smul_eq_smul (α := B) fun x ↦ ?_
  apply FaithfulSMul.algebraMap_injective B B'
  apply FaithfulSMul.algebraMap_injective B' C'
  rw [← IsScalarTower.algebraMap_apply B B' C', IsScalarTower.algebraMap_apply B C C',
    IsGaloisGroup.algebraMap_restrictHom_smul, algebraMap.smul',
    ← IsScalarTower.algebraMap_apply B C C', algebraMap.smul',
    IsGaloisGroup.algebraMap_restrictHom_smul, ← IsScalarTower.algebraMap_apply B B' C']

end restrictHom_eq

theorem IsPrimitiveRoot.isIntegral' {n : ℕ} {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    {μ : L} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) :
    IsIntegral K μ :=
  IsIntegral.tower_top (h.isIntegral hpos)

open IntermediateField in
/-- `E⟮ζ⟯` is a cyclotomic extension of `E` for `ζ` a primitive `n`-th root of unity.

This should replace the existing `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`
in Mathlib: it is more general, dropping the `[Algebra.IsIntegral E F]` hypothesis (`E⟮ζ⟯` only
involves the algebraic element `ζ`, so integrality of the whole `F/E` is irrelevant). -/
theorem IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension' (E : Type*) {F : Type*}
    [Field E] [Field F] [Algebra E F] {n : ℕ} [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} E E⟮ζ⟯ :=
  (isCyclotomicExtension_singleton_iff_eq_adjoin n E F E⟮ζ⟯ hζ).mpr rfl

open IsCyclotomicExtension.Rat in
theorem IsCyclotomicExtension.Rat.map_galEquivZMod_symm_apply {E F : Type*} [Field E] [Field F]
    [NumberField E] [NumberField F] {n : ℕ} [NeZero n] [hE : IsCyclotomicExtension {n} ℚ E]
    [hF : IsCyclotomicExtension {n} ℚ F] (f : E →+* F) (a : (ZMod n)ˣ) (x : E) :
    f ((galEquivZMod n E).symm a x) = (galEquivZMod n F).symm a (f x) := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ E
  have hζp := IsCyclotomicExtension.zeta_pow n ℚ E
  suffices f.toRatAlgHom.comp ((galEquivZMod n E).symm a) =
    ((galEquivZMod n F).symm a).toAlgHom.comp f.toRatAlgHom from AlgHom.congr_fun this x
  refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) ?_
  simp only [Set.eqOn_singleton, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, RingHom.toRatAlgHom_apply,
    Function.comp_apply]
  rw [galEquivZMod_apply_of_pow_eq n _ _ hζp,
    galEquivZMod_apply_of_pow_eq n _ _ (by rw [← map_pow, hζp, map_one]), map_pow,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

@[simp]
theorem IsFractionRing.map_algebraMap {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L]
    {j : A →+* B} (hj : Function.Injective j) (x : A) :
    IsFractionRing.map hj (algebraMap A K x) = algebraMap B L (j x) := by simp [map]

open IsCyclotomicExtension.Rat in
theorem IsCyclotomicExtension.Rat.map_galEquivZMod_symm_smul {E F : Type*} [Field E] [Field F]
    [NumberField E] [NumberField F] {n : ℕ} [NeZero n]
    [hE : IsCyclotomicExtension {n} ℚ E] [hF : IsCyclotomicExtension {n} ℚ F]
    {f : 𝓞 E →+* 𝓞 F} (hf : Function.Injective f) (a : (ZMod n)ˣ) (x : 𝓞 E) :
    f ((galEquivZMod n E).symm a • x) = (galEquivZMod n F).symm a • (f x) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  rw [← IsFractionRing.map_algebraMap (K := E) hf]
  have := map_galEquivZMod_symm_apply (F := F) (IsFractionRing.map hf) a (algebraMap (𝓞 E) E x)
  rwa [IsFractionRing.map_algebraMap] at this

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

/- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
TODO, CHANGE BACK WHEN UPSTREAMING to `Mathlib/Data/Nat/Digits/Lemmas.lean`: there `digitsAppend`
is visible, and the intended proof of `Nat.ofDigits_digitsAppend` is
  `rw [digitsAppend, ofDigits_append_replicate_zero, ofDigits_digits]`.
The proof below via `mapIdx` is only a workaround, because `digitsAppend` does not expose its body
here (it replaces the stub `Nat.digitsAppend_def`, whose `sorry` leaked into the axioms).
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! -/
theorem Nat.ofDigits_digitsAppend (b l n : ℕ) : ofDigits b (digitsAppend b l n) = n := by
  rw [ofDigits_eq_sum_mapIdx, mapIdx_digitsAppend_sum_eq]

/-- Multiplying by `b` modulo `b ^ L.length - 1` rotates the digits of `L` to the right by one
place. -/
theorem Nat.base_mul_ofDigits_modEq {b : ℕ} (hb : 0 < b) (L : List ℕ) :
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
theorem Nat.base_pow_mul_ofDigits_modEq {b : ℕ} (hb : 0 < b) (L : List ℕ) {i : ℕ}
    (hi : i ≤ L.length) :
     b ^ i * ofDigits b L ≡ ofDigits b (L.rotate (L.length - i)) [MOD b ^ L.length - 1] := by
  induction i with
  | zero => simpa using ofDigits_modEq' b b _ rfl L
  | succ n hn =>
    have h := (Nat.ModEq.mul_left b (hn (by lia))).trans <|
      (List.length_rotate _ _) ▸ Nat.base_mul_ofDigits_modEq hb _
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

theorem Nat.sub_one_mul_sum_mul_pow_mod_eq {b l x : ℕ} (hb : 1 < b) (hx : x < b ^ l - 1) :
    (b - 1) * ∑ i ∈ Finset.range l, x * b ^ i % (b ^ l - 1) =
      (b ^ l - 1) * (Nat.digits b x).sum := by
  let L := Nat.digitsAppend b l x
  have hl : (b.digitsAppend l x).length = l := by rw [length_digitsAppend hb _ (by lia)]
  calc
    _ = (b - 1) * ∑ i ∈ Finset.range l, b ^ i * ofDigits b L % (b ^ l - 1) := by
      simp_rw [mul_comm x, L, ofDigits_digitsAppend b l x]
    _ = (b - 1) * ∑ i ∈ Finset.range l, ofDigits b (L.rotate (L.length - i)) := by
      refine congr_arg ((b - 1) * ·) <| Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hl, base_pow_mul_ofDigits_modEq (by lia) _ (by grind)]
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

namespace Ideal

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
  [Module.Finite ℤ S]

/-- A rational prime `p` dividing `absNorm I` lies under a maximal ideal containing `I`. -/
theorem exists_isMaximal_le_of_prime_dvd_absNorm {p : ℕ} (hp : p.Prime) {I : Ideal S}
    (hpI : p ∣ I.absNorm) : ∃ P : Ideal S, P.IsMaximal ∧ I ≤ P ∧ (p : S) ∈ P := by
  obtain ⟨P, hPmax, hPunder, hPI⟩ := exists_isMaximal_dvd_of_dvd_absNorm' hp I hpI
  refine ⟨P, hPmax, Ideal.dvd_iff_le.mp hPI, ?_⟩
  have hmem : (p : ℤ) ∈ P.under ℤ := hPunder ▸ mem_span_singleton_self (p : ℤ)
  rw [mem_under] at hmem
  simpa using hmem

/-- If `I` is coprime to the ideal `(n)` for `n : ℕ`, then `absNorm I` is coprime to `n`. -/
theorem coprime_absNorm_of_isCoprime_span_singleton {n : ℕ} {I : Ideal S}
    (h : IsCoprime I (Ideal.span {(n : S)})) : Nat.Coprime I.absNorm n := by
  by_contra hc
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hc
  obtain ⟨P, hPmax, hIP, hpP⟩ :=
    exists_isMaximal_le_of_prime_dvd_absNorm hp (hpg.trans (Nat.gcd_dvd_left _ _))
  refine hPmax.ne_top (top_le_iff.mp ?_)
  rw [← Ideal.isCoprime_iff_sup_eq.mp h]
  refine sup_le hIP ((span_singleton_le_iff_mem _).mpr ?_)
  obtain ⟨c, hc'⟩ : (p : S) ∣ (n : S) := Nat.cast_dvd_cast (hpg.trans (Nat.gcd_dvd_right _ _))
  rw [hc']
  exact mul_mem_right c P hpP

end Ideal

-- TODO(SKW): convert to the unprimed `Ideal.ramificationIdx` once Mathlib has an unprimed
-- `le_comap_pow_ramificationIdx`. The name is currently taken by a deprecated alias for the primed
-- lemma, and converting here without it would force Dedekind hypotheses on an otherwise
-- `CommRing`-level statement. The call site `Stickelberger.lean` bridges in the meantime.
theorem Ideal.pow_liesOver_of_le_ramificationIdx {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) (P : Ideal S) [P.LiesOver p]
    {i : ℕ} (hi : i + 1 ≤ Ideal.ramificationIdx' p P) :
    (P ^ (i + 1)).LiesOver p := by
  rw [liesOver_iff]
  apply le_antisymm
  · exact le_trans le_comap_pow_ramificationIdx' <| comap_mono (pow_le_pow_right hi)
  · refine le_trans (comap_mono <| pow_le_pow_right (Nat.le_add_left 1 i)) ?_
    rw [pow_one, ← Ideal.under_def, ← Ideal.over_def P p]

instance Ideal.Quotient.isScalarTower_of_liesOver_liesOver {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (Q : Ideal C)
    (P : Ideal B) (p : Ideal A) [Q.LiesOver P] [P.LiesOver p] [Q.LiesOver p] :
    IsScalarTower (A ⧸ p) (B ⧸ P) (C ⧸ Q) := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ Quotient.inductionOn' x fun x ↦ ?_
  have : Quotient.mk'' x = Ideal.Quotient.mk p x := rfl
  simp [this, Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]

theorem Ideal.prime_of_isMaximal {R : Type*} [CommRing R] [CharZero R]
    [Algebra.IsIntegral ℤ R] [IsDedekindDomain R] (I : Ideal R) [I.IsMaximal] :
    Prime I := by
  refine (prime_iff_isPrime (IsMaximal.ne_bot_of_isIntegral_int I)).mpr <| IsMaximal.isPrime' I

theorem Ideal.liesOver_of_absNorm_dvd_prime_pow {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Infinite R] [Algebra.IsIntegral ℤ R] (I : Ideal R) [I.IsPrime] {p k : ℕ}
    [hp : Fact (Nat.Prime p)] (hI : Ideal.absNorm I ∣ p ^ k) :
    I.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : NeZero I := ⟨by
    contrapose hI
    rw [hI, map_zero, Nat.zero_dvd]
    exact NeZero.ne (p ^ k)⟩
  have := (Int.absNorm_under_dvd_absNorm I).trans hI
  rw [Ideal.liesOver_iff, ← Nat.prime_eq_prime_of_dvd_pow (Nat.absNorm_under_prime I)
    hp.out this, Int.ideal_span_absNorm_eq_self]

-- TODO(SKW): upstream to `Mathlib/RingTheory/Ideal/Over.lean`, at the end of the `primesOver`
-- section.
namespace Ideal

variable {R : Type*} (A : Type*) (B : Type*) [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (p : Ideal R)

/-- In a tower `A/B/R`, the primes of `B` over `p` correspond to the pairs `(P, 𝔓)` with `P` a
prime of `A` over `p` and `𝔓` a prime of `B` over `P`. -/
@[expose] def equivPrimesOverPrimesOver :
    p.primesOver B ≃ Σ P : p.primesOver A, P.1.primesOver B where
  toFun 𝔓 := ⟨primesOver.mk p (𝔓.1.under A), primesOver.mk _ 𝔓.1⟩
  invFun P :=
    have := LiesOver.trans P.2.1 P.1.1 p
    primesOver.mk p P.2.1
  right_inv P := Sigma.subtype_ext (Subtype.ext (over_def P.2.1 P.1.1).symm) rfl

@[simp]
theorem coe_equivPrimesOverPrimesOver_symm_apply (x : Σ P : p.primesOver A, P.1.primesOver B) :
    ((equivPrimesOverPrimesOver A B p).symm x : Ideal B) = x.2 :=
  rfl

end Ideal

-- TODO(SKW): upstream both into `Mathlib/NumberTheory/MulChar/Basic.lean`, next to
-- `MulChar.apply_ne_zero_iff`, which is the same statement with `≠ 0` in place of `IsUnit`;
-- Mathlib currently writes `ha.isUnit.map χ` by hand, as in `MulChar/Lemmas.lean:186`.
/-- A multiplicative character sends a unit to a unit. -/
theorem MulChar.isUnit_apply {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    (χ : MulChar R R') {a : R} (ha : IsUnit a) :
    IsUnit (χ a) :=
  ha.map χ

/-- A value of a multiplicative character is a unit precisely at a unit. -/
@[simp]
theorem MulChar.isUnit_apply_iff {R R' : Type*} [CommMonoidWithZero R] [CommMonoidWithZero R']
    [Nontrivial R'] {χ : MulChar R R'} {a : R} :
    IsUnit (χ a) ↔ IsUnit a := by
  refine ⟨fun h ↦ ?_, χ.isUnit_apply⟩
  contrapose h
  rw [map_nonunit χ h]
  exact not_isUnit_zero

namespace FractionalIdeal

section General

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]
  {G : Type*} [Group G] [MulSemiringAction G R] [MulSemiringAction G P] [SMulDistribClass G R P]

/-- The image of a submodule `N ⊆ P` under the ring automorphism induced by `g`. -/
@[expose] def _root_.Submodule.smulSubmodule (g : G) (N : Submodule R P) : Submodule R P where
  carrier := (g • · : P → P) '' N
  add_mem' := by rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩; exact ⟨a + b, N.add_mem ha hb,
    smul_add g a b⟩
  zero_mem' := ⟨0, N.zero_mem, smul_zero g⟩
  smul_mem' c y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨(g⁻¹ • c) • x, N.smul_mem _ hx, ?_⟩
    change g • ((g⁻¹ • c) • x) = c • (g • x)
    rw [smul_distrib_smul, smul_inv_smul]

theorem _root_.Submodule.mem_smulSubmodule {g : G} {N : Submodule R P} {y : P} :
    y ∈ Submodule.smulSubmodule g N ↔ ∃ x ∈ N, g • x = y := Set.mem_image _ _ _

variable (hS : ∀ (g : G) {s : R}, s ∈ S → g • s ∈ S)

include hS

-- TODO(SKW): Mathlib has no action of a group on fractional ideals by ring automorphisms, but
-- two things come close. `Ideal.pointwiseMulSemiringAction` (`Mathlib/RingTheory/Ideal/Pointwise`)
-- is the same construction for ideals (`g • I := I.map (MulSemiringAction.toRingHom _ _ g)`, a
-- `protected def` made an instance in the `Pointwise` scope). `FractionalIdeal.extended`
-- (`Mathlib/RingTheory/FractionalIdeal/Extended`) extends a fractional ideal along a ring
-- homomorphism `f` with `hf : M ≤ N.comap f`; taking `f = MulSemiringAction.toRingHom G R g`, `hf`
-- is exactly `hS g`, so `smulFractional hS g I` should be `I.extended P (hS g)` (the span changes
-- nothing as `g` is bijective), and `extended_one`, `extended_mul`, `extended_extended` would give
-- `smul_one`, `smul_mul`, `mul_smul`. It needs `[IsLocalization S P]`, which holds for
-- `P = FractionRing R` as used for the class group. Untested; to decide before upstreaming, and
-- the names of `smulFractional` and its lemmas are left as they are until then.
/-- The image of a fractional ideal under the ring automorphism induced by `g`. -/
@[expose] def smulFractional (g : G) (I : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨Submodule.smulSubmodule g (I : Submodule R P), by
    obtain ⟨a, ha, H⟩ := I.isFractional
    refine ⟨g • a, hS g ha, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := H x hx
    exact ⟨g • r, by rw [← smul_distrib_smul, ← hr, algebraMap.smul']⟩⟩

theorem coe_smulFractional (g : G) (I : FractionalIdeal S P) :
    (↑(smulFractional hS g I) : Submodule R P) = Submodule.smulSubmodule g (I : Submodule R P) :=
  rfl

theorem mem_smulFractional {g : G} {I : FractionalIdeal S P} {y : P} :
    y ∈ smulFractional hS g I ↔ ∃ x ∈ I, g • x = y := Submodule.mem_smulSubmodule

theorem smulFractional_one (I : FractionalIdeal S P) : smulFractional hS 1 I = I :=
  coeToSubmodule_injective <| Submodule.ext fun y => by
    simp [coe_smulFractional, Submodule.mem_smulSubmodule]

theorem smulFractional_mul (g h : G) (I : FractionalIdeal S P) :
    smulFractional hS (g * h) I
      = smulFractional hS g (smulFractional hS h I) :=
  coeToSubmodule_injective <| Submodule.ext fun y => by
    simp only [coe_smulFractional, Submodule.mem_smulSubmodule]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨h • x, ⟨x, hx, rfl⟩, (mul_smul g h x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, mul_smul g h x⟩

theorem smulFractional_smul_one (g : G) : smulFractional hS g (1 : FractionalIdeal S P) = 1 :=
  coeToSubmodule_injective <| Submodule.ext fun y => by
    simp only [coe_smulFractional, coe_one, Submodule.mem_smulSubmodule, Submodule.mem_one]
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩; exact ⟨g • r, algebraMap.smul' g r P⟩
    · rintro ⟨r, rfl⟩
      exact ⟨algebraMap R P (g⁻¹ • r), ⟨g⁻¹ • r, rfl⟩, by rw [← algebraMap.smul', smul_inv_smul]⟩

theorem smulFractional_smul_mul (g : G) (I J : FractionalIdeal S P) :
    smulFractional hS g (I * J)
      = smulFractional hS g I * smulFractional hS g J :=
  coeToSubmodule_injective <| by
    simp only [coe_smulFractional, coe_mul]
    refine le_antisymm ?_ (Submodule.mul_le.mpr ?_)
    · intro y hy
      rw [Submodule.mem_smulSubmodule] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro a ha b hb
        rw [smul_mul']
        exact Submodule.mul_mem_mul (Submodule.mem_smulSubmodule.mpr ⟨a, ha, rfl⟩)
          (Submodule.mem_smulSubmodule.mpr ⟨b, hb, rfl⟩)
      · intro x y hx hy; rw [smul_add]; exact Submodule.add_mem _ hx hy
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact Submodule.mem_smulSubmodule.mpr ⟨a * b, Submodule.mul_mem_mul ha hb, smul_mul' g a b⟩

/-- The `G`-action on `FractionalIdeal S P` induced by compatible actions on `R` and `P`. -/
@[reducible, expose]
def mulDistribMulAction : MulDistribMulAction G (FractionalIdeal S P) where
  smul := smulFractional hS
  one_smul := smulFractional_one hS
  mul_smul := smulFractional_mul hS
  smul_one := smulFractional_smul_one hS
  smul_mul := smulFractional_smul_mul hS

end General

section FractionRing

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

/-- The `G`-action on `R` extends to a `G`-action on its fraction ring, via the unique
extension of each ring automorphism of `R` to the localization. -/
noncomputable instance : MulSemiringAction G (FractionRing R) where
  smul g x := IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing R) (L := FractionRing R) (MulSemiringAction.toRingEquiv G R g) x
  one_smul x := by
    have : (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
        (MulSemiringAction.toRingEquiv G R (1 : G)) : FractionRing R →+* FractionRing R)
        = RingHom.id _ :=
      IsLocalization.ringHom_ext R⁰ (by ext r; simp)
    exact RingHom.congr_fun this x
  mul_smul g h x := by
    have : (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
        (MulSemiringAction.toRingEquiv G R (g * h)) : FractionRing R →+* FractionRing R) =
        (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
          (MulSemiringAction.toRingEquiv G R g) : FractionRing R →+* FractionRing R).comp
          (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing R) (L := FractionRing R)
            (MulSemiringAction.toRingEquiv G R h)) :=
      IsLocalization.ringHom_ext R⁰ (by ext r; simp)
    exact RingHom.congr_fun this x
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

@[simp]
theorem fractionRing_smul_algebraMap (g : G) (r : R) :
    g • algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (g • r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (MulSemiringAction.toRingEquiv G R g) r

/-- Semilinearity over `R` of the action on the fraction ring. -/
theorem fractionRing_smul_smul (g : G) (a : R) (x : FractionRing R) :
    g • (a • x) = (g • a) • (g • x) := by
  rw [Algebra.smul_def, smul_mul', fractionRing_smul_algebraMap, ← Algebra.smul_def]

instance : SMulDistribClass G R (FractionRing R) where
  smul_distrib_smul := fractionRing_smul_smul

/-- The `G`-action on `R` induces a `G`-action on the fractional ideals of its fraction ring. -/
noncomputable instance instMulDistribMulActionFractionRing :
    MulDistribMulAction G (FractionalIdeal R⁰ (FractionRing R)) :=
  mulDistribMulAction (fun g _ hs => smul_mem_nonZeroDivisors g hs)

@[simp]
theorem mem_smul_fractionRing {g : G} {I : FractionalIdeal R⁰ (FractionRing R)}
    {y : FractionRing R} : y ∈ g • I ↔ ∃ x ∈ I, g • x = y := mem_smulFractional _

open scoped Pointwise in
/-- The coercion `Ideal R → FractionalIdeal R⁰ (FractionRing R)` is `G`-equivariant: the action
on ideals and the action on fractional ideals are compatible. -/
@[simp]
theorem coeIdeal_smul (g : G) (I : Ideal R) :
    (↑(g • I) : FractionalIdeal R⁰ (FractionRing R))
      = g • (I : FractionalIdeal R⁰ (FractionRing R)) := by
  refine coeToSubmodule_injective (Submodule.ext fun y => ?_)
  simp only [coe_coeIdeal, IsLocalization.mem_coeSubmodule]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨algebraMap R (FractionRing R) (g⁻¹ • b),
      ⟨g⁻¹ • b, (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mp hb, rfl⟩, ?_⟩
    change g • algebraMap R (FractionRing R) (g⁻¹ • b) = algebraMap R (FractionRing R) b
    rw [fractionRing_smul_algebraMap, smul_inv_smul]
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g • a, Ideal.smul_mem_pointwise_smul g a I ha,
      (fractionRing_smul_algebraMap g a).symm⟩

/-- The action on fractional ideals is compatible with `spanSingleton`. -/
@[simp]
theorem spanSingleton_smul (g : G) (x : FractionRing R) :
    g • spanSingleton R⁰ x = spanSingleton R⁰ (g • x) := by
  ext y
  simp only [mem_smul_fractionRing, mem_spanSingleton]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨g • a, (fractionRing_smul_smul g a x).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(g⁻¹ • a) • x, ⟨g⁻¹ • a, rfl⟩, by rw [fractionRing_smul_smul, smul_inv_smul]⟩

end FractionRing

end FractionalIdeal

namespace ClassGroup

open scoped nonZeroDivisors Pointwise

open FractionalIdeal

variable {G R : Type*} [Group G] [CommRing R] [IsDedekindDomain R] [MulSemiringAction G R]

attribute [local instance] Units.mulDistribMulActionRight

/-- The `G`-action on fractional ideals preserves the principal ideals. -/
theorem principalIdeals_le_comap (g : G) :
    (toPrincipalIdeal R (FractionRing R)).range ≤
      (toPrincipalIdeal R (FractionRing R)).range.comap
        (MulDistribMulAction.toMulAut G (FractionalIdeal R⁰ (FractionRing R))ˣ g).toMonoidHom := by
  intro I hI
  rw [mem_principal_ideals_iff] at hI
  obtain ⟨x, hx⟩ := hI
  rw [Subgroup.mem_comap, mem_principal_ideals_iff]
  exact ⟨g • x, by rw [← spanSingleton_smul, hx]; rfl⟩

/-- The action of `g` on the class group, as a group homomorphism: descend the pointwise action
on the units of fractional ideals along the quotient by principal ideals. -/
@[expose] noncomputable def mapAut (g : G) : ClassGroup R →* ClassGroup R :=
  QuotientGroup.map (toPrincipalIdeal R (FractionRing R)).range
    (toPrincipalIdeal R (FractionRing R)).range
    (MulDistribMulAction.toMulAut G _ g).toMonoidHom (principalIdeals_le_comap g)

noncomputable instance : SMul G (ClassGroup R) where
  smul g := mapAut g

@[simp]
theorem smul_mk (g : G) (u : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    g • ClassGroup.mk (FractionRing R) u = ClassGroup.mk (FractionRing R) (g • u) := by
  rw [← Quot_mk_eq_mk, ← Quot_mk_eq_mk]
  rfl

@[simp]
theorem smul_mk0 (g : G) (I : (Ideal R)⁰) : g • mk0 I = mk0 (g • I) := by
  rw [← mk_mk0 (K := FractionRing R), smul_mk, ← mk_mk0 (K := FractionRing R)]
  congr 1
  ext1
  rw [Units.coe_smul, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
    nonZeroDivisors.val_smul, coeIdeal_smul]

noncomputable instance : MulDistribMulAction G (ClassGroup R) where
  one_smul c := by obtain ⟨I, rfl⟩ := mk0_surjective c; rw [smul_mk0, one_smul]
  mul_smul g h c := by
    obtain ⟨I, rfl⟩ := mk0_surjective c; rw [smul_mk0, smul_mk0, smul_mk0, mul_smul]
  smul_one g := map_one (mapAut g)
  smul_mul g c d := map_mul (mapAut g) c d

-- The `MulDistribMulAction` reuses the `SMul` instance above (no parallel `SMul` instance /
-- diamond).
example (g : G) (c : ClassGroup R) : g • c = mapAut g c := by
  with_reducible_and_instances rfl

end ClassGroup

namespace FiniteField

open Finset

variable (K : Type*) [Field K] [Fintype K]

local notation "q" => Fintype.card K

-- TODO(SKW): upstream `sum_sdiff_zero` into `Mathlib/FieldTheory/Finite/Basic.lean`, right after
-- `FiniteField.sum_pow_units`.
/-- A sum over the nonzero elements of a finite field is a sum over its units. -/
theorem sum_sdiff_zero {M : Type*} [AddCommMonoid M] [DecidableEq K] (f : K → M) :
    ∑ x ∈ univ \ {0}, f x = ∑ x : Kˣ, f x := by
  let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
  have : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  simp [← this, univ.sum_map φ, φ]

/-- The sum of `x⁻¹ * x ^ (i + 1)` as `x` ranges over a finite field of cardinality `q` is equal
to `-1` if `q - 1 ∣ i`, and to `0` otherwise. -/
theorem sum_inv_mul_pow_succ (i : ℕ) :
    ∑ x : K, x⁻¹ * x ^ (i + 1) = if q - 1 ∣ i then -1 else 0 := by
  classical
  rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, inv_zero, zero_mul, add_zero,
    sum_congr rfl (g := (· ^ i)), sum_sdiff_zero, sum_pow_units K i]
  grind

end FiniteField
