module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Multiplicity

@[expose] public section

/-!
# PRed to Mathlib: `Ideal.span_singleton_dvd_span_singleton_iff_dvd` / `Ideal.emultiplicity_eq_emultiplicity_span` / `Ideal.multiplicity_eq_multiplicity_span`

The declarations in this file were extracted from `SKW.Prereqs.Ideals` and submitted
upstream as Mathlib PR [#40557](https://github.com/leanprover-community/mathlib4/pull/40557).

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit,
this file (and its import in `SKW.Prereqs.Ideals`) should be deleted, and any usages
redirected to the Mathlib versions.
-/

theorem Ideal.span_singleton_dvd_span_singleton_iff_dvd' {R : Type*} [CommRing R] {a b : R} :
    Ideal.span {a} ∣ Ideal.span {b} ↔ a ∣ b := by
  refine ⟨fun ⟨K, hK⟩ ↦ ?_, fun ⟨c, hc⟩ ↦ ⟨Ideal.span {c}, hc ▸ (Ideal.span_singleton_mul_span_singleton a c).symm⟩⟩
  exact Ideal.mem_span_singleton.mp (Ideal.mul_le_left
    ((by rw [mul_comm, ← hK]; exact Ideal.mem_span_singleton.mpr (dvd_refl b))))

theorem Ideal.emultiplicity_span_span {R : Type*} [CommRing R] {a b : R} :
    emultiplicity (Ideal.span {a}) (Ideal.span {b}) = emultiplicity a b := by
  rw [emultiplicity_eq_emultiplicity_iff]
  simp only [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd', implies_true]

theorem Ideal.multiplicity_span_span {R : Type*} [CommRing R] {a b : R} :
    multiplicity (Ideal.span {a}) (Ideal.span {b}) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_span_span

end
