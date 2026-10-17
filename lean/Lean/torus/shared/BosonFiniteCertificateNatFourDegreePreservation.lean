import torus.shared.BosonFiniteCertificateNatFourCOMForm
import torus.shared.BosonFiniteCertificateNatDegreeOrthogonality

/-! True degree preservation and off-diagonal vanishing of the original
four-body source. The normal words, rather than a block matrix declaration,
provide the grading. These are the inputs for a later mixed-degree cutoff. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem natFourTerms_degree_word (terms : List NatFourNormalTerm)
    (hterms : ∀ term ∈ terms, term.creators.length=4 ∧ term.annihilators.length=4 ∧
      term.creators.sum=term.annihilators.sum)
    (d : ℕ) (s : List ℕ) (hs : s.length=4) (hd : s.sum=d) :
    canonicalNatFourTerms terms (scaledWord factorialRootNat s) ∈ natFourDegreeWordSpan d := by
  rw [canonicalNatFourTerms,nat_linear_list_sum_apply]
  apply list_sum_mem
  intro g hg
  obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hg
  simp only [LinearMap.smul_apply]
  apply Submodule.smul_mem
  rw [canonicalNatFourNormalWord_action]
  by_cases hz : wordRemovalWeight s term.annihilators=0
  · simp [hz]
  · have htshape := hterms term ht
    have hlen := eraseWord_length_add s term.annihilators hz
    have he : eraseWord s term.annihilators=[] :=
      List.eq_nil_of_length_eq_zero (by omega)
    have hsum := eraseWord_sum_add s term.annihilators hz
    simp only [he,List.sum_nil,zero_add] at hsum
    simp only [he,List.append_nil]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨term.creators,htshape.1,
      htshape.2.2.trans (hsum.trans hd),rfl⟩

theorem natFourTerms_degree_span (terms : List NatFourNormalTerm)
    (hterms : ∀ term ∈ terms, term.creators.length=4 ∧ term.annihilators.length=4 ∧
      term.creators.sum=term.annihilators.sum) (d : ℕ) :
    natFourDegreeWordSpan d ≤ (natFourDegreeWordSpan d).comap (canonicalNatFourTerms terms) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s,hs,hd,rfl⟩
  exact natFourTerms_degree_word terms hterms d s hs hd

theorem canonicalNatFourOriginalOperator_bihomogeneous (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) :
    (canonicalNatFourOriginalOperator f).IsHomogeneous 4 ∧
      (canonicalNatFourOriginalOperator f).IsWeightedHomogeneous id d := by
  apply natFourDegreeWordSpan_bihomogeneous d
  exact natFourTerms_degree_span natFourOriginalTerms
    (fun term ht => ⟨(natFourOriginalTerms_shape term ht).1,
      (natFourOriginalTerms_shape term ht).2.1,(natFourOriginalTerms_shape term ht).2.2.1⟩)
    d (homogeneous_mem_natFourDegreeWordSpan d f hN hd)

theorem canonicalNatFourOriginalOperator_cross_degree_zero (d e : ℕ) (f g : Core ℕ ℂ)
    (hdf : f.IsWeightedHomogeneous id d) (hNg : g.IsHomogeneous 4)
    (hdg : g.IsWeightedHomogeneous id e) (hde : d ≠ e) :
    natOccupationInner f (canonicalNatFourOriginalOperator g)=0 :=
  natOccupationInner_eq_zero_of_weight_ne d e f (canonicalNatFourOriginalOperator g)
    hdf (canonicalNatFourOriginalOperator_bihomogeneous e g hNg hdg).2 hde

theorem natFourOriginalCOMTerm_cross_degree_zero (d e n : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 4) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 4) (hdg : g.IsWeightedHomogeneous id e) (hde : d ≠ e) :
    natFourOriginalCOMTerm f g n=0 := by
  have hf := canonicalNatFourCOMRaise_iterate_bihomogeneous d n f hNf hdf
  have hg := canonicalNatFourCOMRaise_iterate_bihomogeneous e n g hNg hdg
  rw [natFourOriginalCOMTerm,
    canonicalNatFourOriginalOperator_cross_degree_zero (d+n) (e+n) _ _ hf.2 hg.1 hg.2
      (by omega),mul_zero]

theorem natFourOriginalCOMForm_cross_degree_zero (d e : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 4) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 4) (hdg : g.IsWeightedHomogeneous id e) (hde : d ≠ e) :
    natFourOriginalCOMForm f g=0 := by
  unfold natFourOriginalCOMForm
  simp only [natFourOriginalCOMTerm_cross_degree_zero d e _ f g hNf hdf hNg hdg hde,
    tsum_zero]

#print axioms natFourTerms_degree_word
#print axioms natFourTerms_degree_span
#print axioms canonicalNatFourOriginalOperator_bihomogeneous
#print axioms canonicalNatFourOriginalOperator_cross_degree_zero
#print axioms natFourOriginalCOMTerm_cross_degree_zero
#print axioms natFourOriginalCOMForm_cross_degree_zero
end TorusLean.BosonFiniteCertificate
