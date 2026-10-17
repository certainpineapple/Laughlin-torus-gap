import torus.shared.BosonFiniteCertificateNatCOM
import torus.shared.BosonFiniteCertificateM3SupportTail
import torus.shared.BosonFiniteCertificateThreeOccupationCore

/-! Arbitrarily high descendants of the genuine unbounded-label COM raising
derivation have their true orbital degree. Once that degree exceeds eight,
every original row equals its original pure-pair term on the descendant.
This is an exact source-operator identity, before any physical substitution.
No S/H tail bound or completed torus COM trace is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateConjugation

def threeWordDegreeSpanNat (d : ℕ) : Submodule ℂ (Core ℕ ℂ) :=
  Submodule.span ℂ {f | ∃ s : List ℕ, s.length = 3 ∧ s.sum = d ∧
    f = scaledWord factorialRootNat s}

theorem wordOccupation_degree_nat (s : List ℕ) : (wordOccupation s).degree = s.length := by
  induction s with
  | nil => simp [wordOccupation]
  | cons j s ih => simp only [wordOccupation,map_add,Finsupp.degree_single,List.length_cons,ih]; omega

theorem wordOccupation_weight_nat (s : List ℕ) : Finsupp.weight id (wordOccupation s) = s.sum := by
  induction s with
  | nil => simp [wordOccupation]
  | cons j s ih => simp only [wordOccupation,map_add,Finsupp.weight_single,one_smul,id_eq,List.sum_cons,ih]

theorem scaledWordNat_monomial (s : List ℕ) :
    scaledWord factorialRootNat s = MvPolynomial.monomial (wordOccupation s) (wordScale factorialRootNat s) := by
  simp only [scaledWord,wordPolynomial_eq_monomial,MvPolynomial.smul_monomial,smul_eq_mul,mul_one]

theorem threeWordDegreeSpanNat_bihomogeneous (d : ℕ) (f : Core ℕ ℂ)
    (hf : f ∈ threeWordDegreeSpanNat d) :
    f.IsHomogeneous 3 ∧ f.IsWeightedHomogeneous id d := by
  have hN : threeWordDegreeSpanNat d ≤ MvPolynomial.homogeneousSubmodule ℕ ℂ 3 := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hlen,hsum,rfl⟩
    rw [scaledWordNat_monomial]
    exact MvPolynomial.isHomogeneous_monomial _ ((wordOccupation_degree_nat s).trans hlen)
  have hd : threeWordDegreeSpanNat d ≤ MvPolynomial.weightedHomogeneousSubmodule ℂ id d := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hlen,hsum,rfl⟩
    rw [scaledWordNat_monomial]
    exact MvPolynomial.isWeightedHomogeneous_monomial id (wordOccupation s) _
      ((wordOccupation_weight_nat s).trans hsum)
  exact ⟨hN hf,hd hf⟩

theorem factorialWordScaleNat_ne_zero (s : List ℕ) :
    wordScale factorialRootNat s ≠ 0 := by
  induction s with
  | nil => simp [wordScale]
  | cons j s ih =>
    simp only [wordScale,List.map_cons,List.prod_cons] at ih ⊢
    exact mul_ne_zero (factorialRootNat_ne_zero j) ih

theorem monomial_mem_threeWordDegreeSpanNat (d : ℕ) (n : ℕ →₀ ℕ)
    (hN : n.degree = 3) (hd : Finsupp.weight id n = d) (c : ℂ) :
    MvPolynomial.monomial n c ∈ threeWordDegreeSpanNat d := by
  obtain ⟨a,b,e,he⟩ := occupation_degree_three_word n hN
  have hs : [a,b,e].sum = d := by
    simpa only [he,map_add,Finsupp.weight_single,one_smul,id_eq,List.sum_cons,
      List.sum_nil,Nat.add_zero,Nat.add_assoc] using hd
  have ho : wordOccupation [a,b,e] = n := by
    rw [he]
    simp only [wordOccupation,add_zero,add_assoc]
  have hm : scaledWord factorialRootNat [a,b,e] ∈ threeWordDegreeSpanNat d :=
    Submodule.subset_span ⟨[a,b,e],rfl,hs,rfl⟩
  have h := (threeWordDegreeSpanNat d).smul_mem
    (c / wordScale factorialRootNat [a,b,e]) hm
  simpa only [scaledWord,wordPolynomial_eq_monomial,smul_smul,
    div_mul_cancel₀ _ (factorialWordScaleNat_ne_zero _),ho,
    MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using h

theorem homogeneous_mem_threeWordDegreeSpanNat (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    f ∈ threeWordDegreeSpanNat d := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  apply Submodule.sum_mem
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 3 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  exact monomial_mem_threeWordDegreeSpanNat d n hdeg (hd hc) _

theorem canonicalCOMRaiseNat_span (d : ℕ) :
    threeWordDegreeSpanNat d ≤
      (threeWordDegreeSpanNat (d+1)).comap canonicalCOMRaiseNat := by
  apply Submodule.span_le.mpr
  rintro f ⟨s,hlen,hsum,rfl⟩
  change canonicalCOMRaiseNat (scaledWord factorialRootNat s) ∈ threeWordDegreeSpanNat (d+1)
  rw [canonicalCOMRaiseNat_scaledWord]
  apply list_sum_mem
  intro g hg
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
  exact Submodule.subset_span ⟨w,(raisedWordsNat_length s w hw).trans hlen,
    by rw [raisedWordsNat_sum s w hw,hsum],rfl⟩

theorem canonicalCOMRaiseNat_iterate_span (d k : ℕ) (f : Core ℕ ℂ)
    (hf : f ∈ threeWordDegreeSpanNat d) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f ∈ threeWordDegreeSpanNat (d+k) := by
  induction k with
  | zero => simpa only [Function.iterate_zero,Function.id_def,Nat.add_zero] using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact canonicalCOMRaiseNat_span (d+k) ih

theorem canonicalCOMRaiseNat_iterate_bihomogeneous (d k : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f).IsHomogeneous 3 ∧
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f).IsWeightedHomogeneous id (d+k) := by
  exact threeWordDegreeSpanNat_bihomogeneous (d+k) _
    (canonicalCOMRaiseNat_iterate_span d k f (homogeneous_mem_threeWordDegreeSpanNat d f hN hd))

def canonicalNatRow (t : ℕ) (row : List ℤ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  conjugateOperator factorialRootNat factorialRootNat_ne_zero (paperRowWordOperator t row)

theorem canonicalNatRow_span_tail (d t : ℕ) (row : List ℤ) (hd : 8 < d) :
    threeWordDegreeSpanNat d ≤ LinearMap.ker
      (canonicalNatRow t row - canonicalNatRow t [rowInteger row 0]) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s,hlen,hsum,rfl⟩
  change canonicalNatRow t row (scaledWord factorialRootNat s) -
    canonicalNatRow t [rowInteger row 0] (scaledWord factorialRootNat s) = 0
  exact sub_eq_zero.mpr (m3_conjugated_Nat_row_tail factorialRootNat factorialRootNat_ne_zero
    t row s hlen (by rw [hsum]; exact hd))

/-- True unlimited-label COM iterates, on every bihomogeneous particle/orbital degree-(3,d) polynomial,
are killed by the original row-minus-pure-pair operator above degree eight. -/
theorem canonicalNatRow_descendant_tail (d k t : ℕ) (row : List ℤ)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (htail : 8 < d+k) :
    canonicalNatRow t row ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f) =
      canonicalNatRow t [rowInteger row 0]
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f) := by
  have hm := canonicalCOMRaiseNat_iterate_span d k f
    (homogeneous_mem_threeWordDegreeSpanNat d f hN hd)
  have hz := canonicalNatRow_span_tail (d+k) t row htail hm
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,sub_eq_zero] using hz

#print axioms homogeneous_mem_threeWordDegreeSpanNat
#print axioms canonicalCOMRaiseNat_span
#print axioms canonicalCOMRaiseNat_iterate_span
#print axioms canonicalCOMRaiseNat_iterate_bihomogeneous
#print axioms canonicalNatRow_span_tail
#print axioms canonicalNatRow_descendant_tail
end TorusLean.BosonFiniteCertificate
