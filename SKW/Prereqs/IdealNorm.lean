module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

/-!
# Coprimality of an ideal with a rational integer via the absolute norm

For an order `S` in a number field (`IsDedekindDomain S`, finite free over `ℤ`):

* `Ideal.exists_isMaximal_le_of_prime_dvd_absNorm`: a rational prime `p ∣ absNorm I` lies under a
  maximal ideal containing `I`.
* `Ideal.coprime_absNorm_of_isCoprime_span`: if `I` is coprime to the ideal `(n)` (`n : ℕ`),
  then `absNorm I` is coprime to `n`.
-/

namespace Ideal

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]

/-- A rational prime `p` dividing `absNorm I` lies under a maximal ideal containing `I`. -/
theorem exists_isMaximal_le_of_prime_dvd_absNorm {p : ℕ} (hp : p.Prime) {I : Ideal S}
    (hpI : p ∣ I.absNorm) : ∃ P : Ideal S, P.IsMaximal ∧ I ≤ P ∧ (p : S) ∈ P := by
  obtain ⟨P, hPmax, hPunder, hPI⟩ := exists_isMaximal_dvd_of_dvd_absNorm' hp I hpI
  refine ⟨P, hPmax, Ideal.dvd_iff_le.mp hPI, ?_⟩
  have hmem : (p : ℤ) ∈ P.under ℤ := hPunder ▸ mem_span_singleton_self (p : ℤ)
  rw [mem_under] at hmem
  simpa using hmem

/-- If `I` is coprime to the ideal `(n)` for `n : ℕ`, then `absNorm I` is coprime to `n`. -/
theorem coprime_absNorm_of_isCoprime_span {n : ℕ} {I : Ideal S}
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
