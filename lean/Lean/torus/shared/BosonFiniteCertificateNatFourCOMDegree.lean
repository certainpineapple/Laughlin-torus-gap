import torus.shared.BosonFiniteCertificateNatFourOccupation

/-! Genuine all-level COM descendants in the actual Nat four-particle sector.
The high-degree conclusion is a true one-sided original M4 operator kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

def natFourDegreeWordSpan (d : ℕ) : Submodule ℂ (Core ℕ ℂ) :=
  Submodule.span ℂ {f | ∃ s : List ℕ, s.length=4 ∧ s.sum=d ∧
    f=scaledWord factorialRootNat s}

theorem natFourDegreeWordSpan_bihomogeneous (d : ℕ) (f : Core ℕ ℂ)
    (hf : f ∈ natFourDegreeWordSpan d) :
    f.IsHomogeneous 4 ∧ f.IsWeightedHomogeneous id d := by
  have hN : natFourDegreeWordSpan d ≤ MvPolynomial.homogeneousSubmodule ℕ ℂ 4 := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hlen,hsum,rfl⟩
    rw [scaledWordNat_monomial]
    exact MvPolynomial.isHomogeneous_monomial _ ((wordOccupation_degree_nat s).trans hlen)
  have hd : natFourDegreeWordSpan d ≤ MvPolynomial.weightedHomogeneousSubmodule ℂ id d := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hlen,hsum,rfl⟩
    rw [scaledWordNat_monomial]
    exact MvPolynomial.isWeightedHomogeneous_monomial id (wordOccupation s) _
      ((wordOccupation_weight_nat s).trans hsum)
  exact ⟨hN hf,hd hf⟩

theorem monomial_mem_natFourDegreeWordSpan (d : ℕ) (n : ℕ →₀ ℕ)
    (hN : n.degree = 4) (hd : Finsupp.weight id n = d) (c : ℂ) :
    MvPolynomial.monomial n c ∈ natFourDegreeWordSpan d := by
  obtain ⟨a,b,e,k,he⟩ := occupation_degree_four_word n hN
  have hs : [a,b,e,k].sum = d := by
    simpa only [he,map_add,Finsupp.weight_single,one_smul,id_eq,List.sum_cons,
      List.sum_nil,Nat.add_zero,Nat.add_assoc] using hd
  have ho : wordOccupation [a,b,e,k] = n := by
    rw [he]
    simp only [wordOccupation,add_zero,add_assoc]
  have hm : scaledWord factorialRootNat [a,b,e,k] ∈ natFourDegreeWordSpan d :=
    Submodule.subset_span ⟨[a,b,e,k],rfl,hs,rfl⟩
  have h := (natFourDegreeWordSpan d).smul_mem
    (c / wordScale factorialRootNat [a,b,e,k]) hm
  simpa only [scaledWord,wordPolynomial_eq_monomial,smul_smul,
    div_mul_cancel₀ _ (factorialWordScaleNat_ne_zero _),ho,
    MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using h

theorem homogeneous_mem_natFourDegreeWordSpan (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) :
    f ∈ natFourDegreeWordSpan d := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  apply Submodule.sum_mem
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 4 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  exact monomial_mem_natFourDegreeWordSpan d n hdeg (hd hc) _

theorem canonicalNatFourCOMRaise_span (d : ℕ) :
    natFourDegreeWordSpan d ≤
      (natFourDegreeWordSpan (d+1)).comap canonicalCOMRaiseNat := by
  apply Submodule.span_le.mpr
  rintro f ⟨s,hlen,hsum,rfl⟩
  change canonicalCOMRaiseNat (scaledWord factorialRootNat s) ∈ natFourDegreeWordSpan (d+1)
  rw [canonicalCOMRaiseNat_scaledWord]
  apply list_sum_mem
  intro g hg
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
  exact Submodule.subset_span ⟨w,(raisedWordsNat_length s w hw).trans hlen,
    by rw [raisedWordsNat_sum s w hw,hsum],rfl⟩

theorem canonicalNatFourCOMRaise_iterate_span (d k : ℕ) (f : Core ℕ ℂ)
    (hf : f ∈ natFourDegreeWordSpan d) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f ∈ natFourDegreeWordSpan (d+k) := by
  induction k with
  | zero => simpa only [Function.iterate_zero,Function.id_def,Nat.add_zero] using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact canonicalNatFourCOMRaise_span (d+k) ih

theorem canonicalNatFourCOMRaise_iterate_bihomogeneous (d k : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f).IsHomogeneous 4 ∧
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f).IsWeightedHomogeneous id (d+k) := by
  exact natFourDegreeWordSpan_bihomogeneous (d+k) _
    (canonicalNatFourCOMRaise_iterate_span d k f (homogeneous_mem_natFourDegreeWordSpan d f hN hd))

theorem canonicalNatFourOriginalOperator_descendant_tail (d n : ℕ)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d)
    (h : 16<d+n) :
    canonicalNatFourOriginalOperator
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f)=0 := by
  have hh := canonicalNatFourCOMRaise_iterate_bihomogeneous d n f hN hd
  exact canonicalNatFourOriginalOperator_homogeneous_tail (d+n) _ hh.1 hh.2 h

#print axioms natFourDegreeWordSpan_bihomogeneous
#print axioms monomial_mem_natFourDegreeWordSpan
#print axioms homogeneous_mem_natFourDegreeWordSpan
#print axioms canonicalNatFourCOMRaise_span
#print axioms canonicalNatFourCOMRaise_iterate_span
#print axioms canonicalNatFourCOMRaise_iterate_bihomogeneous
#print axioms canonicalNatFourOriginalOperator_descendant_tail
end TorusLean.BosonFiniteCertificate
