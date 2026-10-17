import torus.shared.BosonFiniteCertificateNatFourFactorizedNormal
import torus.shared.BosonFiniteCertificateNatFourCOMDegree
import torus.shared.BosonFiniteCertificateNatPairHamiltonianCore

/-! Rank-source resolution of the actual original finite normal tensor on
every particle-homogeneous N4 polynomial with unrestricted natural labels.
The left test polynomial is arbitrary. The annihilator orbital factorial
denominator is derived from the original rescaling and occupation metric;
no finite block matrix defines the source or its homogeneous carrier. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

theorem natFour_scaledWord_inner_complete (s labels : List ℕ)
    (hlen : s.length=labels.length) :
    natOccupationInner (scaledWord factorialRootNat labels) (scaledWord factorialRootNat s)=
      (wordRemovalWeight s labels : ℂ)*(natFourOrbitalMetric labels : ℂ) := by
  by_cases hp : s.Perm labels
  · have ho : wordOccupation labels=wordOccupation s :=
      (natFourOccupation_eq_iff_perm s labels).mpr hp |>.symm
    rw [natFour_scaledWord_inner,if_pos ho,
      natFour_removal_input_perm s labels labels hp,natFour_removal_self,
      natFourMultiplicity_eq_weight]
    simp only [natFourWordMetric,Nat.cast_mul]
  · have ho : wordOccupation labels≠wordOccupation s := by
      intro ho
      exact hp ((natFourOccupation_eq_iff_perm s labels).mp ho.symm)
    rw [natFour_scaledWord_inner,if_neg ho,
      natFour_removal_zero_of_not_perm s labels hlen hp]
    simp

private theorem natFour_rank_orbital_metric_ne_zero (labels : List ℕ) :
    (natFourOrbitalMetric labels : ℂ)≠0 := by
  have h : natFourOrbitalMetric labels≠0 := by
    induction labels with
    | nil => simp [natFourOrbitalMetric]
    | cons j labels ih =>
      simpa only [natFourOrbitalMetric,List.map_cons,List.prod_cons] using
        mul_ne_zero (Nat.factorial_ne_zero j) ih
  exact_mod_cast h

private theorem canonicalNatFourNormalWord_rank_word (creators annihilators s : List ℕ)
    (hlen : s.length=annihilators.length) :
    canonicalNatFourNormalWord creators annihilators (scaledWord factorialRootNat s)=
      (natOccupationInner (scaledWord factorialRootNat annihilators)
        (scaledWord factorialRootNat s)/(natFourOrbitalMetric annihilators : ℂ)) •
          scaledWord factorialRootNat creators := by
  rw [canonicalNatFourNormalWord_action,natFour_scaledWord_inner_complete s annihilators hlen,
    mul_div_cancel_right₀ _ (natFour_rank_orbital_metric_ne_zero annihilators)]
  by_cases hz : wordRemovalWeight s annihilators=0
  · simp only [hz,Nat.cast_zero,zero_smul]
  · have he : eraseWord s annihilators=[] := List.eq_nil_of_length_eq_zero (by
      have hh := eraseWord_length_add s annihilators hz
      omega)
    rw [he,List.append_nil]

private def natFour_rank_word_span : Submodule ℂ (Core ℕ ℂ) :=
  Submodule.span ℂ {f | ∃ s : List ℕ, s.length=4 ∧ f=scaledWord factorialRootNat s}

private theorem natFour_rank_homogeneous_mem (f : Core ℕ ℂ) (hN : f.IsHomogeneous 4) :
    f ∈ natFour_rank_word_span := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  apply Submodule.sum_mem
  intro n hn
  have hc : f.coeff n≠0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree=4 := by
    by_contra he
    exact hc (hN.coeff_eq_zero he)
  have hi : natFourDegreeWordSpan (Finsupp.weight id n) ≤ natFour_rank_word_span := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hs,hd,rfl⟩
    exact Submodule.subset_span ⟨s,hs,rfl⟩
  exact hi (monomial_mem_natFourDegreeWordSpan (Finsupp.weight id n) n hdeg rfl _)

theorem canonicalNatFourNormalWord_rank_action (creators annihilators : List ℕ)
    (ha : annihilators.length=4) (g : Core ℕ ℂ) (hN : g.IsHomogeneous 4) :
    canonicalNatFourNormalWord creators annihilators g=
      (natOccupationInner (scaledWord factorialRootNat annihilators) g /
        (natFourOrbitalMetric annihilators : ℂ)) • scaledWord factorialRootNat creators := by
  have hg := natFour_rank_homogeneous_mem g hN
  clear hN
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hs,rfl⟩ := hf
    exact canonicalNatFourNormalWord_rank_word creators annihilators s (hs.trans ha.symm)
  | zero => simp only [map_zero,natOccupationInner_zero_right,zero_div,zero_smul]
  | add f g hf hg ihf ihg =>
    rw [map_add,ihf,ihg,natOccupationInner_add_right,add_div,add_smul]
  | smul c f hf ih =>
    simp only [map_smul,ih,natOccupationInner_smul_right,smul_smul,mul_div_assoc]

theorem canonicalNatFourNormalWord_rank_form (creators annihilators : List ℕ)
    (ha : annihilators.length=4) (f g : Core ℕ ℂ) (hN : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourNormalWord creators annihilators g)=
      (natFourOrbitalMetric annihilators : ℂ)⁻¹ *
        star (natOccupationInner (scaledWord factorialRootNat creators) f) *
        natOccupationInner (scaledWord factorialRootNat annihilators) g := by
  rw [canonicalNatFourNormalWord_rank_action creators annihilators ha g hN,
    natOccupationInner_smul_right,← natOccupationInner_conj_symm
      (scaledWord factorialRootNat creators) f]
  ring

theorem canonicalNatFourTerms_rank_form (terms : List NatFourNormalTerm)
    (hterms : ∀ term ∈ terms, term.annihilators.length=4)
    (f g : Core ℕ ℂ) (hN : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourTerms terms g)=
      (terms.map fun term => (term.coefficient : ℂ)/(natFourOrbitalMetric term.annihilators : ℂ) *
        star (natOccupationInner (scaledWord factorialRootNat term.creators) f) *
        natOccupationInner (scaledWord factorialRootNat term.annihilators) g).sum := by
  rw [canonicalNatFourTerms,nat_linear_list_sum_apply,natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term ht
  rw [LinearMap.smul_apply,natOccupationInner_smul_right,
    canonicalNatFourNormalWord_rank_form term.creators term.annihilators (hterms term ht) f g hN]
  ring

theorem canonicalNatFourOriginalOperator_rank_form (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 4) :
    natOccupationInner f (canonicalNatFourOriginalOperator g)=
      (natFourOriginalTerms.map fun term =>
        (term.coefficient : ℂ)/(natFourOrbitalMetric term.annihilators : ℂ) *
        star (natOccupationInner (scaledWord factorialRootNat term.creators) f) *
        natOccupationInner (scaledWord factorialRootNat term.annihilators) g).sum :=
  canonicalNatFourTerms_rank_form natFourOriginalTerms
    (fun term ht => (natFourOriginalTerms_shape term ht).2.1) f g hN

#print axioms natFour_scaledWord_inner_complete
#print axioms canonicalNatFourNormalWord_rank_action
#print axioms canonicalNatFourNormalWord_rank_form
#print axioms canonicalNatFourTerms_rank_form
#print axioms canonicalNatFourOriginalOperator_rank_form
end TorusLean.BosonFiniteCertificate
