import torus.shared.BosonFiniteCertificateNatFourOccupation

/-! Complete four-particle homogeneous blocks over arbitrary Nat orbitals.
The enumeration follows the sorted occupation words, with repeated labels.
Its completeness is derived from particle and orbital homogeneity, never
assumed from a proposed relative-coordinate family. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

/-- Three bounded loops determine the fourth label from the true total degree.
The fourth label is admitted only when the subtraction is non-truncating. -/
def natFourBasis (d : ℕ) : List (List ℕ) :=
  (List.range (d+1)).flatMap fun a =>
    (List.range (d+1)).flatMap fun b =>
      ((List.range (d+1)).filter fun c =>
        decide (a ≤ b ∧ b ≤ c ∧ c ≤ d-a-b-c ∧ a+b+c ≤ d)).map
          fun c => [a,b,c,d-a-b-c]

theorem natFourBasis_mem_sorted (d a b c e : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hs : a+b+c+e = d) :
    [a,b,c,e] ∈ natFourBasis d := by
  apply List.mem_flatMap.mpr
  refine ⟨a,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_map.mpr
  refine ⟨c,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),?_⟩,?_⟩
  · apply decide_eq_true
    omega
  · have he : d-a-b-c=e := by omega
    simp only [he]

theorem natFourBasis_shape (d : ℕ) (s : List ℕ) (hs : s ∈ natFourBasis d) :
    s.length = 4 ∧ s.sum = d := by
  rcases List.mem_flatMap.mp hs with ⟨a,ha,hs⟩
  rcases List.mem_flatMap.mp hs with ⟨b,hb,hs⟩
  rcases List.mem_map.mp hs with ⟨c,hc,rfl⟩
  have hh := of_decide_eq_true (List.mem_filter.mp hc).2
  change 4=4 ∧ a + (b + (c + ((d-a-b-c)+0))) = d
  omega

/-- Actual Nat occupations, not a preselected span, exhaust this enumeration. -/
theorem natFourBasis_occupation_complete (d : ℕ) (n : ℕ →₀ ℕ)
    (hN : n.degree=4) (hd : Finsupp.weight id n=d) :
    ∃ s ∈ natFourBasis d, wordOccupation s=n := by
  obtain ⟨a,b,c,e,hab,hbc,hce,he⟩ := occupation_degree_four_sorted n hN
  have hs : a+b+c+e=d := by
    rw [he] at hd
    simpa only [map_add,Finsupp.weight_single,one_smul,id_eq] using hd
  refine ⟨[a,b,c,e],natFourBasis_mem_sorted d a b c e hab hbc hce hs,?_⟩
  rw [he]
  simp only [wordOccupation,add_zero,add_assoc]

def natFourWordBlockLinear {ι : Type*} [Fintype ι] (basis : ι → List ℕ) :
    (ι → ℂ) →ₗ[ℂ] Core ℕ ℂ where
  toFun := natFourWordBlock basis
  map_add' x y := by simp [natFourWordBlock,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp [natFourWordBlock,Finset.smul_sum,smul_smul]

theorem natFour_scaledWord_mem_block_range {ι : Type*} [Fintype ι]
    (basis : ι → List ℕ) (a : ι) :
    scaledWord factorialRootNat (basis a) ∈ LinearMap.range (natFourWordBlockLinear basis) := by
  classical
  refine ⟨Pi.single a 1,?_⟩
  change natFourWordBlock basis (Pi.single a 1) = _
  simp [natFourWordBlock,Pi.single_apply]

/-- An exact finite enumeration suffices for full polynomial exhaustiveness;
the coefficients of every monomial are reconstructed using a nonzero genuine
sqrt-factorial scale. Linear independence is a separate statement. -/
theorem natFour_homogeneous_eq_block_of_enumeration {m : ℕ}
    (d : ℕ) (basis : Fin m → List ℕ) (henum : List.ofFn basis = natFourBasis d)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) :
    ∃ x : Fin m → ℂ, natFourWordBlock basis x = f := by
  have hf : f ∈ LinearMap.range (natFourWordBlockLinear basis) := by
    rw [← MvPolynomial.support_sum_monomial_coeff f]
    apply Submodule.sum_mem
    intro n hn
    have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
    have hdeg : n.degree=4 := by
      by_contra he
      exact hc (hN.coeff_eq_zero he)
    obtain ⟨s,hs,ho⟩ := natFourBasis_occupation_complete d n hdeg (hd hc)
    rw [← henum] at hs
    obtain ⟨a,ha⟩ := List.mem_ofFn.mp hs
    have hm := natFour_scaledWord_mem_block_range basis a
    rw [ha] at hm
    have h := (LinearMap.range (natFourWordBlockLinear basis)).smul_mem
      (f.coeff n / wordScale factorialRootNat s) hm
    simpa only [scaledWord,wordPolynomial_eq_monomial,smul_smul,
      div_mul_cancel₀ _ (factorialWordScaleNat_ne_zero _),ho,
      MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using h
  exact hf

/-- Actual monomial coefficient extraction, using distinct occupations and
nonzero physical scales. No inverse Gram matrix is involved. -/
theorem natFourWordBlock_coefficient {ι : Type*} [Fintype ι]
    (basis : ι → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a)))
    (x : ι → ℂ) (a : ι) :
    (natFourWordBlock basis x).coeff (wordOccupation (basis a)) =
      x a * wordScale factorialRootNat (basis a) := by
  classical
  simp [natFourWordBlock, natFour_scaledWord_monomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, hinj.eq_iff]

theorem natFourWordBlock_injective {ι : Type*} [Fintype ι]
    (basis : ι → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a))) :
    Function.Injective (natFourWordBlock basis) := by
  intro x y h
  funext a
  have hc := congrArg (fun f : Core ℕ ℂ => f.coeff (wordOccupation (basis a))) h
  rw [natFourWordBlock_coefficient basis hinj, natFourWordBlock_coefficient basis hinj] at hc
  exact mul_right_cancel₀ (factorialWordScaleNat_ne_zero (basis a)) hc

theorem natFourWordBlock_zero {ι : Type*} [Fintype ι] (basis : ι → List ℕ) :
    natFourWordBlock basis (0 : ι → ℂ) = 0 := by
  simp [natFourWordBlock]

theorem natFourWordBlock_eq_zero_iff {ι : Type*} [Fintype ι]
    (basis : ι → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a))) (x : ι → ℂ) :
    natFourWordBlock basis x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact natFourWordBlock_injective basis hinj (h.trans (natFourWordBlock_zero basis).symm)
  · rintro rfl
    exact natFourWordBlock_zero basis

#print axioms natFourBasis_mem_sorted
#print axioms natFourBasis_shape
#print axioms natFourBasis_occupation_complete
#print axioms natFour_scaledWord_mem_block_range
#print axioms natFour_homogeneous_eq_block_of_enumeration
#print axioms natFourWordBlock_coefficient
#print axioms natFourWordBlock_injective
#print axioms natFourWordBlock_zero
#print axioms natFourWordBlock_eq_zero_iff
end TorusLean.BosonFiniteCertificate
