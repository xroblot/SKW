module

public import Mathlib.NumberTheory.Cyclotomic.Basic

set_option linter.style.header false

/-!
# PRed to Mathlib: `E⟮ζ⟯` is cyclotomic without integrality

The declaration in this file was extracted from `SKW.Prereqs.Stickelberger` and submitted upstream
as Mathlib PR [#45992](https://github.com/leanprover-community/mathlib4/pull/45992), which drops the
hypothesis `[Algebra.IsIntegral E F]` from
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`.

Once that PR is merged and the `lake-manifest.json` pin is bumped past the merge commit, this file
and its import in `SKW.Prereqs.Stickelberger` should be deleted, and the usages of
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension'` redirected to the unprimed lemma.
-/

public section

open IntermediateField in
/-- `E⟮ζ⟯` is a cyclotomic extension of `E` for `ζ` a primitive `n`-th root of unity.

This should replace the existing `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`
in Mathlib: it is more general, dropping the `[Algebra.IsIntegral E F]` hypothesis (`E⟮ζ⟯` only
involves the algebraic element `ζ`, so integrality of the whole `F/E` is irrelevant). -/
theorem IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension' (E : Type*) {F : Type*}
    [Field E] [Field F] [Algebra E F] {n : ℕ} [NeZero n] {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    IsCyclotomicExtension {n} E E⟮ζ⟯ :=
  (isCyclotomicExtension_singleton_iff_eq_adjoin n E F E⟮ζ⟯ hζ).mpr rfl
