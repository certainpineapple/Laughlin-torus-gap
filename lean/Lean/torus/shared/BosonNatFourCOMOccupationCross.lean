import torus.shared.BosonFiniteCertificateNatFourCOMNormalization

/-! True occupation-inner COM orthogonality for the complete Nat source.
The relative vectors are arbitrary lowering vacua; their mutual Gram remains
on the diagonal. No finite occupation cutoff or relative orthogonality is used. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourCOMOccupationCross
open TorusLean.Boson TorusLean.BosonFiniteCertificate

private theorem iterate_inner_ne (n m : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) (hLf : canonicalCOMLowerNat f=0)
    (hLg : canonicalCOMLowerNat g=0) (hne : n≠m) :
    natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m] g)=0 := by
  induction n generalizing m with
  | zero =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Ne.symm hne)
    exact canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero_symm m g f hLf
  | succ n ih =>
    cases m with
    | zero => exact canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero n f g hLg
    | succ m =>
      rw [Function.iterate_succ_apply',canonicalCOMRaiseNat_adjoint,
        canonicalCOMNat_lower_iterate_particle 4 m g hNg hLg,
        natOccupationInner_smul_right,ih m (by omega),mul_zero]

theorem natFour_COM_iterate_cross (n m : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4)
    (hLf : canonicalCOMLowerNat f = 0) (hLg : canonicalCOMLowerNat g = 0) :
    natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[m] g) =
      if n=m then ((4:ℂ)^n*(n.factorial:ℂ))*natOccupationInner f g else 0 := by
  by_cases h : n=m
  · subst m
    rw [if_pos rfl,natFour_COM_iterate_inner n f g hNg hLg]
  · rw [if_neg h,iterate_inner_ne n m f g hNg hLf hLg h]

theorem natFour_normalized_COM_cross (n m : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4)
    (hLf : canonicalCOMLowerNat f = 0) (hLg : canonicalCOMLowerNat g = 0) :
    natOccupationInner (natFourNormalizedCOMDescendant n f)
      (natFourNormalizedCOMDescendant m g) =
      if n=m then natOccupationInner f g else 0 := by
  by_cases h : n=m
  · subst m
    simpa only [ite_true] using natFourNormalizedCOMDescendant_inner n f g hNg hLg
  · rw [natFourNormalizedCOMDescendant,natFourNormalizedCOMDescendant,
      natOccupationInner_smul_left,natOccupationInner_smul_right,
      natFour_COM_iterate_cross n m f g hNg hLf hLg]
    simp only [h,ite_false,mul_zero]

#print axioms natFour_COM_iterate_cross
#print axioms natFour_normalized_COM_cross
end TorusLean.Shared.BosonNatFourCOMOccupationCross
