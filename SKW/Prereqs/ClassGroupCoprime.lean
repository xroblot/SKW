module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

open scoped nonZeroDivisors

@[expose] public section

/-!
# Coprime integral representatives in an ideal class

In a Dedekind domain, every ideal class contains an integral ideal coprime to a given nonzero
ideal (`ClassGroup.exists_mk0_eq_and_isCoprime`).
-/

namespace ClassGroup

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Every ideal class contains an integral ideal coprime to any given nonzero ideal `J`. -/
theorem exists_mk0_eq_and_isCoprime (C : ClassGroup R) {J : Ideal R} (hJ : J ≠ ⊥) :
    ∃ I : (Ideal R)⁰, mk0 I = C ∧ IsCoprime (I : Ideal R) J := by
  by_cases hJtop : J = ⊤
  · obtain ⟨I, rfl⟩ := mk0_surjective C
    exact ⟨I, rfl, by rw [Ideal.isCoprime_iff_sup_eq, hJtop, sup_top_eq]⟩
  obtain ⟨I₀, hI₀⟩ := mk0_surjective C⁻¹
  have hI₀0 : (I₀ : Ideal R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I₀.prop
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (Ideal.mul_le_right : (I₀ : Ideal R) * J ≤ I₀) (mul_ne_zero hI₀0 hJ)
  have hspan_le : Ideal.span {a} ≤ (I₀ : Ideal R) := ha ▸ le_sup_right
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hspan_le
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, sup_bot_eq] at ha
    exact hJtop (mul_left_cancel₀ hI₀0 (ha.trans (Ideal.mul_top _).symm))
  have hI0 : I ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hI
    exact ha0 (Ideal.span_singleton_eq_bot.mp hI)
  have hImem : I ∈ (Ideal R)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hI0
  have hspan_mem : Ideal.span {a} ∈ (Ideal R)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (mt Ideal.span_singleton_eq_bot.mp ha0)
  refine ⟨⟨I, hImem⟩, ?_, ?_⟩
  · have key : mk0 I₀ * mk0 ⟨I, hImem⟩ = 1 := by
      rw [← map_mul]
      exact (congrArg mk0 (Subtype.ext hI.symm : I₀ * ⟨I, hImem⟩ = ⟨Ideal.span {a}, hspan_mem⟩)).trans
        ((mk0_eq_one_iff hspan_mem).mpr ⟨⟨a, rfl⟩⟩)
    rw [hI₀] at key
    exact (inv_mul_eq_one.mp key).symm
  · rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    refine mul_left_cancel₀ hI₀0 ?_
    rw [Ideal.mul_sup, Ideal.mul_top, ← hI, ha]

end ClassGroup
