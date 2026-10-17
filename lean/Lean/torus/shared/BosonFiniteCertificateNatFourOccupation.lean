import torus.shared.BosonFiniteCertificateNatFourSupport
import torus.shared.BosonFiniteCertificateNatCOMTail

/-! Four-particle occupation words exhaust the actual particle-homogeneous
polynomial sector. This removes the word-span premise from the original M4
high-degree annihilation result. Low-degree matrix enumeration and the
relative lowering kernel are not claimed here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

/-- Split one genuine occupation from a four-particle monomial and use the
already proved three-particle decomposition, with all repetitions allowed. -/
theorem occupation_degree_four_word {ι : Type*} (n : ι →₀ ℕ) (hn : n.degree = 4) :
    ∃ a b c d, n = Finsupp.single a 1 + Finsupp.single b 1 +
      Finsupp.single c 1 + Finsupp.single d 1 := by
  classical
  obtain ⟨u, hu, hu1⟩ := Finsupp.exists_le_degree_eq n 1 (by omega)
  obtain ⟨v, huv⟩ := le_iff_exists_add.mp hu
  have hv : v.degree = 3 := by
    have h := congrArg Finsupp.degree huv
    simp only [map_add, hn, hu1] at h
    omega
  have eu : u ∈ Set.range (fun a : ι => Finsupp.single a 1) := by
    rw [Finsupp.range_single_one]
    exact hu1
  obtain ⟨a,rfl⟩ := eu
  obtain ⟨b,c,d,hv⟩ := occupation_degree_three_word v hv
  exact ⟨a,b,c,d,by rw [huv,hv]; dsimp only; ac_rfl⟩

/-- Sorting is a permutation of four occupation summands, not a restriction
to distinct orbitals. This is the input for later complete block enumeration. -/
theorem occupation_degree_four_sorted {ι : Type*} [LinearOrder ι]
    (n : ι →₀ ℕ) (hn : n.degree = 4) :
    ∃ a b c d, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
      n = Finsupp.single a 1 + Finsupp.single b 1 +
        Finsupp.single c 1 + Finsupp.single d 1 := by
  classical
  obtain ⟨u, hu, hu1⟩ := Finsupp.exists_le_degree_eq n 1 (by omega)
  obtain ⟨v, huv⟩ := le_iff_exists_add.mp hu
  have hv : v.degree = 3 := by
    have h := congrArg Finsupp.degree huv
    simp only [map_add, hn, hu1] at h
    omega
  have eu : u ∈ Set.range (fun a : ι => Finsupp.single a 1) := by
    rw [Finsupp.range_single_one]
    exact hu1
  obtain ⟨a,rfl⟩ := eu
  obtain ⟨b,c,d,hbc,hcd,hv⟩ := occupation_degree_three_sorted v hv
  have hn : n = Finsupp.single a 1 + Finsupp.single b 1 +
      Finsupp.single c 1 + Finsupp.single d 1 := by rw [huv,hv]; dsimp only; ac_rfl
  by_cases hab : a ≤ b
  · exact ⟨a,b,c,d,hab,hbc,hcd,hn⟩
  · by_cases hac : a ≤ c
    · exact ⟨b,a,c,d,le_of_not_ge hab,hac,hcd,hn.trans (by ac_rfl)⟩
    · by_cases had : a ≤ d
      · exact ⟨b,c,a,d,hbc,le_of_not_ge hac,had,hn.trans (by ac_rfl)⟩
      · exact ⟨b,c,d,a,hbc,hcd,le_of_not_ge had,hn.trans (by ac_rfl)⟩

theorem natFour_monomial_mem_tail (n : ℕ →₀ ℕ) (c : ℂ)
    (hn : n.degree = 4) (hd : 16 < Finsupp.weight id n) :
    MvPolynomial.monomial n c ∈ natFourHighDegreeWordSpan := by
  obtain ⟨a,b,e,d,he⟩ := occupation_degree_four_word n hn
  have ho : wordOccupation [a,b,e,d] = n := by
    rw [he]
    simp only [wordOccupation,add_zero,add_assoc]
  have hs : 16 < [a,b,e,d].sum := by
    rw [← wordOccupation_weight_nat,ho]
    exact hd
  have hm : scaledWord factorialRootNat [a,b,e,d] ∈ natFourHighDegreeWordSpan :=
    Submodule.subset_span ⟨[a,b,e,d],rfl,hs,rfl⟩
  have h := natFourHighDegreeWordSpan.smul_mem
    (c / wordScale factorialRootNat [a,b,e,d]) hm
  simpa only [scaledWord,wordPolynomial_eq_monomial,smul_smul,
    div_mul_cancel₀ _ (factorialWordScaleNat_ne_zero _),ho,
    MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using h

/-- The real four-particle high-degree polynomial sector lies in the source
word span; the carrier premise is a proved consequence of homogeneity. -/
theorem natFour_homogeneous_mem_tail (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) (h : 16 < d) :
    f ∈ natFourHighDegreeWordSpan := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  apply Submodule.sum_mem
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 4 := by
    by_contra he
    exact hc (hN.coeff_eq_zero he)
  apply natFour_monomial_mem_tail n _ hdeg
  rw [hd hc]
  exact h

/-- True original M4 kills every Nat-labelled bihomogeneous N=4 polynomial
above degree sixteen, rather than only vanishing in a same-block cross-form. -/
theorem canonicalNatFourOriginalOperator_homogeneous_tail (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) (h : 16 < d) :
    canonicalNatFourOriginalOperator f = 0 :=
  canonicalNatFourOriginalOperator_tail_span (natFour_homogeneous_mem_tail d f hN hd h)

#print axioms occupation_degree_four_word
#print axioms occupation_degree_four_sorted
#print axioms natFour_monomial_mem_tail
#print axioms natFour_homogeneous_mem_tail
#print axioms canonicalNatFourOriginalOperator_homogeneous_tail
end TorusLean.BosonFiniteCertificate
