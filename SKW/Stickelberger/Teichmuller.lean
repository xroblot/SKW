module

public import SKW.Misc

@[expose] public section

variable {R : Type*} [CommRing R] (n : ℕ) (I : Ideal R)

/--
For `I` an ideal of `R`, the group morphism from the roots of unity of `R`
of order `n` to `(R ⧸ I)ˣ`.
-/
def rootsOfUnity.mapQuot : (rootsOfUnity n R) →* (R ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).restrict _


@[simp]
theorem rootsOfUnity.coe_mapQuot (x : rootsOfUnity n R) :
    (rootsOfUnity.mapQuot n I x).val = Ideal.Quotient.mk I x.val := rfl

variable {n I} (hbij : Function.Bijective (rootsOfUnity.mapQuot n I))

noncomputable def teichmuller : MulChar (R ⧸ I) R :=
  MulChar.ofUnitHom <| (rootsOfUnity n R).subtype.comp (MulEquiv.ofBijective _ hbij).symm.toMonoidHom

attribute [local instance] Ideal.Quotient.field

open Classical

theorem teichmuller_apply (x : R ⧸ I) :
    teichmuller hbij x =
      if hx : IsUnit x then
        (((MulEquiv.ofBijective (rootsOfUnity.mapQuot n I) hbij).symm hx.unit).val : R) else 0 := rfl

theorem teichmuller_eq_one (hI : I = ⊤) :
    teichmuller hbij = 1 := by
  rw [← Ideal.Quotient.subsingleton_iff] at hI
  exact MulChar.eq_one_iff.mpr fun x ↦ by simp [teichmuller_apply, isUnit_iff_eq_one, Units.eq_one x]

theorem teichmuller_apply_zero (hI : I ≠ ⊤) :
    teichmuller hbij 0 = 0 := by
  have : Nontrivial (R ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hI
  rw [teichmuller_apply, dif_neg not_isUnit_zero]

theorem isUnit_teichmuller_zpow_apply [I.IsMaximal] (a : ℤ) (x : (R ⧸ I)ˣ) :
    IsUnit ((teichmuller hbij ^ a) x) := by
  rw [MulChar.zpow_apply_coe_eq_apply_zpow, teichmuller_apply, dif_pos (Units.isUnit _)]
  exact Units.isUnit _

theorem teichmuller_zpow_apply_ne_zero [Nontrivial R] [I.IsMaximal] (a : ℤ) (x : (R ⧸ I)ˣ) :
    (teichmuller hbij ^ a) x ≠ 0 :=
  (isUnit_teichmuller_zpow_apply hbij a x).ne_zero

theorem teichmuller_mk_eq [I.IsMaximal] (x : R ⧸ I) :
    Ideal.Quotient.mk I (teichmuller hbij x) = x := by
  by_cases hI : I = ⊤
  · have := Ideal.Quotient.subsingleton_iff.mpr hI
    rw [teichmuller_eq_one _ hI, MulChar.one_apply (isUnit_of_subsingleton x),
      Subsingleton.eq_one x, map_one]
  by_cases hx : x = 0
  · rw [hx, teichmuller_apply_zero _ hI, map_zero]
  lift x to (R ⧸ I)ˣ using Ne.isUnit hx
  simp [teichmuller_apply, IsUnit.unit_of_val_units, ← rootsOfUnity.coe_mapQuot]

theorem orderOf_teichmuller [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    orderOf (teichmuller hbij) = n := by
  refine (orderOf_eq_iff (NeZero.pos _)).mpr ⟨?_, fun m h₁ h₂ ↦ MulChar.ne_one_iff.mpr ?_⟩
  · ext
    simpa [teichmuller, MulChar.pow_apply_coe] using (mem_rootsOfUnity' _ _).mp <| SetLike.coe_mem _
  · refine ⟨rootsOfUnity.mapQuot n I hζ.toRootsOfUnity, ?_⟩
    rw [teichmuller, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.ofBijective_symm_apply_apply, Subgroup.subtype_apply,
      IsPrimitiveRoot.val_toRootsOfUnity_coe, ne_eq, hζ.pow_eq_one_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt h₂ h₁

theorem orderOf_teichmuller_zpow [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) (a : ℤ) :
    orderOf (teichmuller hbij ^ a) ∣ n := by
  nth_rewrite 2 [← orderOf_teichmuller hbij hζ]
  exact orderOf_dvd_of_mem_zpowers <| Subgroup.zpow_mem_zpowers (teichmuller hbij) a

theorem exists_nat_teichmuller_zpow_eq_pow [IsDomain R] [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (a : ℤ) (x : (R ⧸ I)ˣ) :
    ∃ m : ℕ, (teichmuller hbij ^ a) x = ζ ^ m := by
  have : ((teichmuller hbij ^ a) x) ^ n = 1 := by
    obtain ⟨t, ht⟩ := orderOf_teichmuller_zpow hbij hζ a
    have := DFunLike.congr_fun (pow_orderOf_eq_one (teichmuller hbij ^ a)) ↑x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
    nth_rewrite 2 [ht]
    rw [pow_mul, this, one_pow]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one this
  exact ⟨a, ha.symm⟩

theorem map_teichmuller_zpow_eq [IsDomain R] [NeZero n] {S : Type*}
    [CommRing S] {F : Type*} [FunLike F S S] [RingHomClass F S S] (σ : F) (f : R →+* S)
    (m : ℕ) {ζ : R} (hm : m ≠ 0) (hζ : IsPrimitiveRoot ζ n) (hσ : σ (f ζ) = (f ζ) ^ m) (a : ℤ)
    (x : R ⧸ I) :
    σ ((teichmuller hbij ^ a).ringHomComp f x) = (teichmuller hbij ^ (a * m)).ringHomComp f x  := by
  by_cases hx : IsUnit x
  · lift x to (R ⧸ I)ˣ using hx
    obtain ⟨t , ht⟩ := exists_nat_teichmuller_zpow_eq_pow hbij hζ a x
    rw [MulChar.ringHomComp_apply, ht, map_pow, map_pow, hσ,MulChar.ringHomComp_apply,
      zpow_mul, zpow_natCast, MulChar.pow_apply' _ hm, ht, map_pow, map_pow, pow_right_comm]
  · simp [MulChar.map_nonunit _ hx]
