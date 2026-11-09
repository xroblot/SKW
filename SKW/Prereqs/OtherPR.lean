module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.FieldTheory.Galois.Abelian

set_option linter.style.header false

@[expose] public section

open NumberField Ideal IntermediateField

/-- If a prime is unramified in `F₁/ℚ` and in `F₂/ℚ`, then it is unramified in
`(F₁ ⊔ F₂)/ℚ`. From Mathlib PR
[#36843](https://github.com/leanprover-community/mathlib4/pull/36843). -/
theorem Ideal.ramificationIdx_sup_eq_one {L : Type*} [Field L] [NumberField L]
    {F₁ F₂ : IntermediateField ℚ L} (htop : F₁ ⊔ F₂ = ⊤) {p : Ideal ℤ} {P₁ : Ideal (𝓞 F₁)}
    {P₂ : Ideal (𝓞 F₂)} {P : Ideal (𝓞 L)} [P₁.LiesOver p] [P₂.LiesOver p]
    [P.LiesOver P₁] [P.LiesOver P₂] (h₁ : ramificationIdx P₁ ℤ = 1)
    (h₂ : ramificationIdx P₂ ℤ = 1) (hp : p ≠ ⊥) :
    ramificationIdx P ℤ = 1 := by
  sorry

/-- Let `C` be an inertia ring of `P` and `𝓟` the prime of `C` below `P`. Then `𝓟` is unramified
over `A`. From Mathlib PR [#35808](https://github.com/leanprover-community/mathlib4/pull/35808). -/
theorem Ideal.IsInertiaRing.ramificationIdx_eq {A B : Type*} [CommRing A] [CommRing B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] (P : Ideal B) [P.IsPrime]
    (C : Type*) [CommRing C] [Algebra C B] [Algebra A B] [Algebra A C] [IsScalarTower A C B]
    {p : Ideal A} [P.LiesOver p] (𝓟 : Ideal C) [P.LiesOver 𝓟] [P.IsInertiaRing G C]
    [IsGaloisGroup G A B] [Module.Finite A B] [IsDomain A] [IsDomain B] [IsDomain C]
    [Module.Flat A B] [Module.Flat C B] [Ring.HasFiniteQuotients A] [Ring.HasFiniteQuotients B]
    (hp : p ≠ ⊥) :
    𝓟.ramificationIdx A = 1 := by
  sorry

/-- Let `C` be an inertia ring of `P` and `𝓟` the prime of `C` below `P`. Then `P` is the only
prime of `B` above `𝓟`. From Mathlib PR
[#35808](https://github.com/leanprover-community/mathlib4/pull/35808). -/
theorem Ideal.IsInertiaRing.primesOver_eq_singleton {B : Type*} [CommRing B] (G : Type*) [Group G]
    [MulSemiringAction G B] (P : Ideal B) (C : Type*) [CommRing C] [Algebra C B] (𝓟 : Ideal C)
    [P.LiesOver 𝓟] [P.IsInertiaRing G C] [P.IsPrime] [Finite (Ideal.inertia G P)] :
    Ideal.primesOver 𝓟 B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, fun Q ⟨_, _⟩ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝓟 P Q (Ideal.inertia G P)
  exact Ideal.inertia_le_stabilizer _ σ.prop

open Ideal in
/-- Let `C` be an inertia ring of `P` and `𝓟` the prime of `C` below `P`. Then the inertia degree
of `𝓟` in `B` equals `1`. From Mathlib PR
[#35808](https://github.com/leanprover-community/mathlib4/pull/35808), where `P` is maximal. -/
theorem Ideal.IsInertiaRing.inertiaDegIn_eq {B : Type*} [CommRing B] (G : Type*) [Group G]
    [Finite G] [MulSemiringAction G B] (P : Ideal B) [P.IsPrime] (C : Type*) [CommRing C]
    [Algebra C B] (𝓟 : Ideal C) [P.LiesOver 𝓟] [P.IsInertiaRing G C] [Ring.HasFiniteQuotients B]
    [Algebra.IsIntegral C B] (hP : P ≠ ⊥) :
    inertiaDegIn 𝓟 B = 1 := by
  sorry

/-- The inertia field of `P` in `L/K`: the subfield of `L` fixed by the inertia subgroup of `P`.
From Mathlib PR [#35991](https://github.com/leanprover-community/mathlib4/pull/35991). -/
def Ideal.inertiaField (K L : Type*) [Field K] [Field L] [Algebra K L] {B : Type*} [CommRing B]
    (P : Ideal B) [MulSemiringAction Gal(L/K) B] : IntermediateField K L :=
  fixedField (inertia Gal(L/K) P)

/-- Let `F` be an intermediate field of `L/K`. The inertia field of `P` for `L/F` is the
compositum of `F` with the inertia field of `P` for `L/K`. From Mathlib PR
[#35991](https://github.com/leanprover-community/mathlib4/pull/35991). -/
theorem Ideal.inertiaField_restrictScalars (K L : Type*) [Field K] [Field L] [Algebra K L]
    {B : Type*} [CommRing B] (P : Ideal B) [MulSemiringAction Gal(L/K) B]
    (F : IntermediateField K L) [Algebra B L] [IsFractionRing B L]
    [SMulDistribClass Gal(L/K) B L] [MulSemiringAction Gal(L/F) B] [SMulDistribClass Gal(L/F) B L]
    [FiniteDimensional K L] [IsGalois K L] :
    (P.inertiaField F L).restrictScalars K = F ⊔ P.inertiaField K L := by
  sorry

/-- The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p`
in `B`. From Mathlib PR [#36733](https://github.com/leanprover-community/mathlib4/pull/36733). -/
theorem Ideal.finrank_inertiaField_top {A B : Type*} (K L : Type*) [Field K] [Field L]
    [Algebra K L] [CommRing B] (P : Ideal B) [MulSemiringAction Gal(L/K) B] [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [Algebra B L] [IsFractionRing B L]
    [SMulDistribClass Gal(L/K) B L] [Algebra A K] [IsFractionRing A K] [Algebra A B] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsIntegral A B] [Module.Finite A B]
    [Module.Flat A B] [FiniteDimensional K L] [IsGalois K L] (p : Ideal A) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] [PerfectField p.ResidueField] :
    Module.finrank (P.inertiaField K L) L = p.ramificationIdxIn B := by
  sorry

/-- The discriminant of a quadratic field is a fundamental discriminant. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.isFundamentalDiscr_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  sorry

/-- The discriminant is a complete invariant of quadratic fields. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.nonempty_algEquiv_iff_discr_eq (K F : Type*) [Field K] [Field F]
    [NumberField K] [NumberField F] (hK : Module.finrank ℚ K = 2)
    (hF : Module.finrank ℚ F = 2) :
    Nonempty (K ≃ₐ[ℚ] F) ↔ NumberField.discr K = NumberField.discr F := by
  sorry

/-- `√(discr K)` lies in `K`. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.exists_sq_eq_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ∃ x : K, x ^ 2 = (NumberField.discr K : K) := by
  sorry

/-- The discriminant of a quadratic field is not `1`. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.discr_ne_one (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    NumberField.discr K ≠ 1 := by
  sorry

/-- The discriminant of a quadratic field is not a square. From Mathlib PR
[#43490](https://github.com/leanprover-community/mathlib4/pull/43490), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.not_isSquare_discr (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ¬ IsSquare (NumberField.discr K) := by
  sorry

/-- A quadratic field is totally real iff its discriminant is positive. From Mathlib PR
[#43493](https://github.com/leanprover-community/mathlib4/pull/43493), where it is stated for
`[Algebra.IsQuadraticExtension ℚ K]` (#42554). -/
theorem NumberField.QuadraticField.isTotallyReal_iff_discr_pos (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    IsTotallyReal K ↔ 0 < NumberField.discr K := by
  sorry

/-- Instance form of `NumberField.QuadraticField.isTotallyReal_iff_discr_pos`: a totally real
quadratic field has positive discriminant. -/
theorem NumberField.QuadraticField.discr_pos (K : Type*) [Field K] [NumberField K]
    [IsTotallyReal K] (hK : Module.finrank ℚ K = 2) :
    0 < NumberField.discr K :=
  (isTotallyReal_iff_discr_pos K hK).mp ‹_›

/-- Reduction modulo `ζ - 1` is invariant under every ring endomorphism of `𝓞 K`, where `ζ` is a
primitive `n`-th root of unity. From Mathlib PR
[#45512](https://github.com/leanprover-community/mathlib4/pull/45512). -/
theorem IsCyclotomicExtension.Rat.quotientMk_span_zeta_sub_one_comp (n : ℕ) {K : Type*} [Field K]
    [NumberField K] [NeZero n] [IsCyclotomicExtension {n} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (σ : 𝓞 K →+* 𝓞 K) :
    (Ideal.Quotient.mk (span {hζ.toInteger - 1})).comp σ = Ideal.Quotient.mk _ := by
  sorry

theorem IsCyclotomicExtension.Rat.quotientMk_span_zeta_sub_one_comp_apply (n : ℕ) {K : Type*}
    [Field K] [NumberField K] [NeZero n] [IsCyclotomicExtension {n} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (σ : 𝓞 K →+* 𝓞 K) (x : 𝓞 K) :
    Ideal.Quotient.mk (span {hζ.toInteger - 1}) (σ x) = Ideal.Quotient.mk _ x :=
  RingHom.congr_fun (quotientMk_span_zeta_sub_one_comp n hζ σ) x
