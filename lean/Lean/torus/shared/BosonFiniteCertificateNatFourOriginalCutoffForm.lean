import torus.shared.BosonFiniteCertificateNatFourDegreePreservation
import torus.shared.BosonFiniteCertificateNatMixedComparison

/-! The original M4 cross form on a completely arbitrary true N4 ket has
exactly seventeen orbital blocks. This follows from the actual finite
polynomial projections, genuine source grading, and the one-sided source
tail. The bra is arbitrary; no relative restriction or matrix is involved. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

private theorem natFour_original_component_zero_outside (d : ℕ) (g : Core ℕ ℂ)
    (hd : d ∉ g.support.image (Finsupp.weight id)) : natOrbitalComponent d g=0 := by
  classical
  apply MvPolynomial.ext
  intro n
  by_cases hw : Finsupp.weight id n=d
  · have hc : g.coeff n=0 := by
      by_contra hc
      exact hd (Finset.mem_image.mpr ⟨n,MvPolynomial.mem_support_iff.mpr hc,hw⟩)
    simp [natOrbitalComponent,MvPolynomial.coeff_weightedHomogeneousComponent,hw,hc]
  · simp [natOrbitalComponent,MvPolynomial.coeff_weightedHomogeneousComponent,hw]

theorem canonicalNatFourOriginalOperator_component_form (d : ℕ) (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourOriginalOperator (natOrbitalComponent d g))=
      natOccupationInner (natOrbitalComponent d f)
        (canonicalNatFourOriginalOperator (natOrbitalComponent d g)) := by
  have hw := (canonicalNatFourOriginalOperator_bihomogeneous d (natOrbitalComponent d g)
    (natOrbitalComponent_particle 4 d g hNg) (natOrbitalComponent_weighted d g)).2
  have h := congrArg star (natOccupationInner_orbitalComponent_right d
    (canonicalNatFourOriginalOperator (natOrbitalComponent d g)) f hw)
  simpa only [natOccupationInner_conj_symm] using h.symm

/-- The finite-support calculation is proved for an abstract linear source.
This avoids reducing the large literal original source while checking the
finite union and linearity proof. The public instance below discharges both
hypotheses for the genuine original source. -/
private theorem natFour_linearSource_cross_cutoff
    (A : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ) (f g : Core ℕ ℂ)
    (hc : ∀ d, natOccupationInner f (A (natOrbitalComponent d g))=
      natOccupationInner (natOrbitalComponent d f) (A (natOrbitalComponent d g)))
    (ht : ∀ d, 16<d → A (natOrbitalComponent d g)=0) :
    natOccupationInner f (A g)=
      ∑ d ∈ Finset.range 17, natOccupationInner (natOrbitalComponent d f)
        (A (natOrbitalComponent d g)) := by
  classical
  let s : Finset ℕ := g.support.image (Finsupp.weight id)
  let F : ℕ → ℂ := fun d => natOccupationInner (natOrbitalComponent d f)
    (A (natOrbitalComponent d g))
  have hfinite : natOccupationInner f (A g)=∑ d ∈ s, F d := by
    calc
      _ = natOccupationInner f (A (∑ d ∈ s, natOrbitalComponent d g)) := by
        rw [natOrbitalComponent_finite_sum]
      _ = ∑ d ∈ s, natOccupationInner f (A (natOrbitalComponent d g)) := by
        rw [map_sum,natOccupationInner_sum_right]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hc d
  have hl : (∑ d ∈ s, F d)=∑ d ∈ s ∪ Finset.range 17, F d := by
    apply Finset.sum_subset Finset.subset_union_left
    intro d hd hnot
    dsimp only [F]
    rw [natFour_original_component_zero_outside d g hnot,map_zero,natOccupationInner_zero_right]
  have hr : (∑ d ∈ Finset.range 17, F d)=∑ d ∈ s ∪ Finset.range 17, F d := by
    apply Finset.sum_subset Finset.subset_union_right
    intro d hd hnot
    have hh : ¬d<17 := fun hlt => hnot (Finset.mem_range.mpr hlt)
    dsimp only [F]
    rw [ht d (by omega),natOccupationInner_zero_right]
  exact hfinite.trans (hl.trans hr.symm)

/-- All components absent from g are zero and all degrees above sixteen
are annihilated by the true original normal-ordered operator. -/
theorem canonicalNatFourOriginalOperator_cross_cutoff (f g : Core ℕ ℂ)
    (hNg : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourOriginalOperator g)=
      ∑ d ∈ Finset.range 17, natOccupationInner (natOrbitalComponent d f)
        (canonicalNatFourOriginalOperator (natOrbitalComponent d g)) := by
  apply natFour_linearSource_cross_cutoff canonicalNatFourOriginalOperator f g
  · intro d
    exact canonicalNatFourOriginalOperator_component_form d f g hNg
  · intro d hd
    exact canonicalNatFourOriginalOperator_homogeneous_tail d (natOrbitalComponent d g)
      (natOrbitalComponent_particle 4 d g hNg) (natOrbitalComponent_weighted d g) hd

#print axioms canonicalNatFourOriginalOperator_component_form
#print axioms canonicalNatFourOriginalOperator_cross_cutoff
end TorusLean.BosonFiniteCertificate
