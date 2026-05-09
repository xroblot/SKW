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

theorem exists_nat_teichmuller_eq_pow [IsDomain R] [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (x : (R ⧸ I)ˣ) :
    ∃ a : ℕ, teichmuller hbij x = ζ ^ a := by
  have : (teichmuller hbij x) ^ n = 1 := by
    have := DFunLike.congr_fun (pow_orderOf_eq_one (teichmuller hbij)) ↑x
    rwa [MulChar.pow_apply_coe, MulChar.one_apply_coe, orderOf_teichmuller hbij hζ] at this
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one this
  exact ⟨a, ha.symm⟩

theorem map_teichmuller_apply_eq_pow [IsDomain R] [NeZero n] {S : Type*}
    [CommRing S] {F : Type*} [FunLike F S S] [RingHomClass F S S] (σ : F) (f : R →+* S) 
    (m : ℕ) {ζ : R} (hm : m ≠ 0) (hζ : IsPrimitiveRoot ζ n) (hσ : σ (f ζ) = (f ζ) ^ m) (x : R ⧸ I) :
    σ ((teichmuller hbij).ringHomComp f x) = (teichmuller hbij ^ m).ringHomComp f x  := by
  let a := (hζ.isUnit (NeZero.ne _)).unit
  by_cases hx : IsUnit x
  · lift x to (R ⧸ I)ˣ using hx
    obtain ⟨a , ha⟩ := exists_nat_teichmuller_eq_pow hbij hζ x
    simp [MulChar.ringHomComp_apply, MulChar.pow_apply' _ hm, ha, hσ, pow_right_comm]
  · simp [MulChar.map_nonunit _ hx]
