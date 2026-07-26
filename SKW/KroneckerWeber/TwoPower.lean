module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

public import SKW.KroneckerWeber.Basic
public import SKW.KroneckerWeber.Reduction
public import SKW.Prereqs.AlgebraMisc
public import SKW.Prereqs.CMField
public import SKW.Prereqs.CyclotomicField

@[expose] public section

/-!
# Kronecker-Weber for 2-power cyclic extensions

The `p = 2` case of the reduction to prime power degree, handled by **Lemmermeyer's argument**
(Prop. 1.5). Unlike the odd case (`prop_kw_odd_prime_power`), this needs **no** Kummer/class-group
machinery: `ℚ(ζ_{2^n})/ℚ` is not cyclic (`(ℤ/2^n)ˣ ≅ ℤ/2 × ℤ/2^{n-2}`), so the odd-case template
"unique subfield of each degree" fails; instead the argument is elementary, driven by the
classification of quadratics and the compositum comparison.

## Structure

- `prop_kw_2_quadratic`: every quadratic extension of `ℚ` unramified outside `2` lies in
  `ℚ(ζ_8) = ℚ⟮ξ 8⟯` (the three are `ℚ(i)`, `ℚ(√-2)`, `ℚ(√2)`).
- `prop_kw_2_quadratic_real_unique`: there is a *unique* totally real quadratic extension of `ℚ`
  unramified outside `2` (namely `ℚ(√2) = ℚ(ζ_8)⁺`). This is the pigeonhole that forces cyclicity of
  the relevant compositum in the real case.
- `prop_kw_2_power_real`: the **real case** — a totally real cyclic `2^m` extension unramified
  outside `2` is contained in `ℚ(ζ_{2^{m+2}})`.
- `prop_kw_2_power`: the **general case**, reduced to the real case via the CM field `K(i)`.

The engines are `kw_cyclic_compositum`, the non-cyclic-`2`-group fact
`IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic`, and Mathlib's CM-field API
(`maximalRealSubfield`/`complexConj`, with cyclotomic fields CM via
`IsCyclotomicExtension.Rat.isCMField`).
-/

open NumberField Ideal

noncomputable section

open IntermediateField in
/-- The quadratic extensions of `ℚ` unramified outside `2` are exactly `ℚ(i)`, `ℚ(√-2)`, `ℚ(√2)`,
all contained in `ℚ(ζ_8) = ℚ⟮ξ 8⟯`. (Proof: `ℚ(√d)`, `d` squarefree, ramifies at `ℓ` iff
`ℓ ∣ disc`, with `disc = d` or `4d`; unramified outside `2` forces `disc` a power of `2`, i.e.
`d ∈ {-1, 2, -2}`; and `ζ_8` supplies `i = ζ_8²`, `√2 = ζ_8 + ζ_8⁻¹`, `√-2 = i√2`.) -/
theorem prop_kw_2_quadratic {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] (hK : Module.finrank ℚ K = 2)
    (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ 8⟯ := by
  sorry

open IntermediateField in
/-- Uniqueness of the real quadratic: any two *totally real* quadratic extensions of `ℚ` unramified
outside `2` coincide (both equal `ℚ(√2) = ℚ(ζ_8)⁺`). Follows from `prop_kw_2_quadratic`: both lie in
`ℚ(ζ_8)`, are real of degree `2`, and `ℚ(√2)` is the only real quadratic subfield of `ℚ(ζ_8)`. This
is the pigeonhole used in `prop_kw_2_power_real`. -/
theorem prop_kw_2_quadratic_real_unique {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n)
    (K₁ : IntermediateField ℚ A) [NumberField K₁] [IsGalois ℚ K₁] [IsTotallyReal K₁]
    (hK₁ : Module.finrank ℚ K₁ = 2) (hKram₁ : UnramifiedOutside K₁ 2)
    (K₂ : IntermediateField ℚ A) [NumberField K₂] [IsGalois ℚ K₂] [IsTotallyReal K₂]
    (hK₂ : Module.finrank ℚ K₂ = 2) (hKram₂ : UnramifiedOutside K₂ 2) :
    K₁ = K₂ := by
  sorry

open IntermediateField in
/-- **Real case.** A totally real cyclic extension of `ℚ` of degree `2^m` unramified outside `2` is
contained in `ℚ(ζ_{2^{m+2}}) = ℚ⟮ξ (2^(m+2))⟯`.

Plan: let `K' := ℚ(ζ_{2^{m+2}})⁺` (the maximal real subfield, cyclic of degree `2^m`, unramified
outside `2`). If `K ⊔ K'` were not cyclic, its Galois group (a non-cyclic finite abelian `2`-group)
would have two distinct index-`2` subgroups
(`IsPGroup.exists_index_eq_prime_ne_of_not_isCyclic`), giving two distinct quadratic subfields —
both totally real (`K ⊔ K'` is totally real) and unramified outside `2` — contradicting
`prop_kw_2_quadratic_real_unique`. So `K ⊔ K'` is cyclic, and `kw_cyclic_compositum` gives
`K ≤ K' ≤ ℚ⟮ξ (2^(m+2))⟯`. -/
theorem prop_kw_2_power_real {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ) (hm : 0 < m)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    [IsTotallyReal K] (hK : Module.finrank ℚ K = 2 ^ m) (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ (2 ^ (m + 2))⟯ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAbelianGalois ℚ K := IsAbelianGalois.of_isCyclic ℚ K
  have hCcyc : IsCyclotomicExtension {2 ^ (m + 2)} ℚ ℚ⟮ξ (2 ^ (m + 2))⟯ :=
    (hξ (2 ^ (m + 2))).adjoinSimple_isCyclotomicExtension (2 ^ (m + 2)) ℚ A
  have : NumberField ℚ⟮ξ (2 ^ (m + 2))⟯ := IsCyclotomicExtension.numberField {2 ^ (m + 2)} ℚ _
  -- `K' = ℚ(ζ_{2^{m+2}})⁺`, the maximal real subfield: cyclic of degree `2^m`, totally real,
  -- unramified outside `2`, contained in `ℚ(ζ_{2^{m+2}})`.
  obtain ⟨K', hK'le, hK'deg, hK'gal, hK'cyc, hK'ram, hK'real⟩ :
      ∃ K' : IntermediateField ℚ A, K' ≤ ℚ⟮ξ (2 ^ (m + 2))⟯ ∧ Module.finrank ℚ K' = 2 ^ m ∧
        IsGalois ℚ K' ∧ IsCyclic Gal(K'/ℚ) ∧ UnramifiedOutside K' 2 ∧ IsTotallyReal K' := sorry
  have : NumberField K' :=
    let : Algebra K' ℚ⟮ξ (2 ^ (m + 2))⟯ := (inclusion hK'le).toAlgebra
    NumberField.of_tower ℚ ℚ⟮ξ (2 ^ (m + 2))⟯ _
  have : IsGalois ℚ K' := hK'gal
  have : IsCyclic Gal(K'/ℚ) := hK'cyc
  have : IsTotallyReal K' := hK'real
  have : IsAbelianGalois ℚ K' := IsAbelianGalois.of_isCyclic ℚ K'
  -- The compositum `K ⊔ K'` is totally real (both factors are).
  have hsupreal : IsTotallyReal ↑(K ⊔ K') := sorry
  refine (kw_le_of_unique_prime_subfield K K' hK hK'deg hKram hK'ram ?_).trans hK'le
  intro F₁ F₂ _ _ _ _ _ _ hle₁ hle₂ hf₁ hf₂ hr₁ hr₂
  let : Algebra F₁ ↑(K ⊔ K') := (inclusion hle₁).toAlgebra
  let : Algebra F₂ ↑(K ⊔ K') := (inclusion hle₂).toAlgebra
  have : IsScalarTower ℚ F₁ ↑(K ⊔ K') :=
    IsScalarTower.of_algebraMap_eq fun x => ((inclusion hle₁).commutes x).symm
  have : IsScalarTower ℚ F₂ ↑(K ⊔ K') :=
    IsScalarTower.of_algebraMap_eq fun x => ((inclusion hle₂).commutes x).symm
  have : IsTotallyReal F₁ := IsTotallyReal.of_algebra F₁ ↑(K ⊔ K')
  have : IsTotallyReal F₂ := IsTotallyReal.of_algebra F₂ ↑(K ⊔ K')
  exact prop_kw_2_quadratic_real_unique hξ F₁ hf₁ hr₁ F₂ hf₂ hr₂

open IntermediateField in
/-- Every cyclic extension of `ℚ` of degree `2ᵐ` unramified outside `2` is cyclotomic: contained in
`ℚ(ζ_{2^{m+2}}) = ℚ⟮ξ (2^(m+2))⟯` inside the ambient field `A`.

Plan (reduce the general case to `prop_kw_2_power_real`): if `K` is totally real, apply the real
case directly. Otherwise pass to `K(i) = K · ℚ(i)`, a CM field with maximal real subfield `M`
(`K(i) = M(i)`); `M` is real, cyclic, of `2`-power degree, and unramified outside `2`, so the real
case makes `M` — and hence `K` — cyclotomic. -/
theorem prop_kw_2_power {A : Type*} [Field A] [CharZero A] {ξ : ℕ → A}
    (hξ : ∀ n, IsPrimitiveRoot (ξ n) n) (m : ℕ) (hm : 0 < m)
    (K : IntermediateField ℚ A) [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)]
    (hK : Module.finrank ℚ K = 2 ^ m) (hKram : UnramifiedOutside K 2) :
    K ≤ ℚ⟮ξ (2 ^ (m + 2))⟯ := by
  sorry

end

end
