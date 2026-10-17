import torus.shared.ThermalCoherentBosonRowFourCanonicalSourceCoefficient

/-! Literal original column-pair rank forms. The sources are the actual
normalized pair-COM polynomials multiplied by the original spectator labels.
No restriction of mode labels or particle state is needed for these finite
coefficient identities. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

def fourCanonicalRankTerm (f g : Core ℕ ℂ) (term : NatFourNormalTerm) : ℂ :=
  (term.coefficient:ℂ)/(natFourOrbitalMetric term.annihilators:ℂ) *
    star (natOccupationInner (scaledWord factorialRootNat term.creators) f) *
    natOccupationInner (scaledWord factorialRootNat term.annihilators) g

/-- Finite original term lists are expanded without evaluating the large table. -/
theorem fourCanonical_terms_flatMap {A : Type*} (l : List A)
    (F : A → List NatFourNormalTerm) (f g : Core ℕ ℂ) :
    ((l.flatMap F).map (fourCanonicalRankTerm f g)).sum =
      (l.map fun a => ((F a).map (fourCanonicalRankTerm f g)).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,
      List.map_cons,List.sum_cons]

private theorem wordScale_real (s : List ℕ) :
    star (wordScale factorialRootNat s)=wordScale factorialRootNat s := by
  induction s with
  | nil => simp [wordScale]
  | cons a s ih =>
    simp only [wordScale,List.map_cons,List.prod_cons,star_mul] at ih ⊢
    rw [ih]
    simp only [factorialRootNat,Complex.star_def,Complex.conj_ofReal]
    ring

/-- One term uses the literal creator and annihilator lists from the table. -/
theorem fourCanonical_originalTerm_cross (t p j p' j' a b : ℕ) (c c' : ℤ)
    (f g : Core ℕ ℂ) :
    fourCanonicalRankTerm f g (natFourOriginalTerm t p j p' j' a b c c') =
      (alphaOf t p j c:ℂ)*(alphaOf t p' j' c':ℂ)*
        natPairNormalization p*natPairNormalization p'*
        pairCoefficientNat p a*pairCoefficientNat p' b *
        star (natOccupationInner (wordPolynomial [a,p-a,j,p'+j'-t]) f) *
        natOccupationInner (wordPolynomial [p+j-t,j',b,p'-b]) g := by
  have h := fourCanonical_originalTerm_coefficient t p j p' j' a b c c'
  unfold fourCanonicalRankTerm
  simp only [scaledWord,natOccupationInner_smul_left,star_mul,star_star,wordScale_real]
  calc
    _ = (((natFourOriginalTerm t p j p' j' a b c c').coefficient:ℂ) /
        (natFourOrbitalMetric (natFourOriginalTerm t p j p' j' a b c c').annihilators:ℂ) *
        wordScale factorialRootNat (natFourOriginalTerm t p j p' j' a b c c').creators *
        wordScale factorialRootNat (natFourOriginalTerm t p j p' j' a b c c').annihilators) *
        star (natOccupationInner (wordPolynomial [a,p-a,j,p'+j'-t]) f) *
        natOccupationInner (wordPolynomial [p+j-t,j',b,p'-b]) g := by
      simp only [natFourOriginalTerm]
      ring
    _ = _ := by rw [h]

private theorem word_four_swap (i j a b : ℕ) :
    (wordPolynomial [i,j,a,b] : Core ℕ ℂ)=wordPolynomial [a,b,j,i] := by
  simp only [wordPolynomial,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  ring

/-- Summing both ordered pair labels gives the exact crossed pair/spectator
sources. There is no extra half or spectator normalization in this identity. -/
theorem fourCanonical_column_pair_cross (t p j p' j' : ℕ) (c c' : ℤ)
    (f g : Core ℕ ℂ) :
    ((natFourColumnPairTerms t (some (p,j),c) (some (p',j'),c')).map
      (fourCanonicalRankTerm f g)).sum =
      (alphaOf t p j c:ℂ)*(alphaOf t p' j' c':ℂ)*
        star (natOccupationInner ((pairCOMSeed p*MvPolynomial.X j)*
          MvPolynomial.X (p'+j'-t)) f) *
        natOccupationInner ((pairCOMSeed p'*MvPolynomial.X j')*
          MvPolynomial.X (p+j-t)) g := by
  simp only [natFourColumnPairTerms,fourCanonical_terms_flatMap,
    List.map_map,Function.comp_def,nat_pair_list_range_sum]
  simp_rw [fourCanonical_originalTerm_cross,word_four_swap (p+j-t) j']
  rw [fourCanonical_pair_word,fourCanonical_pair_word]
  simp only [natOccupationInner_sum_left,natOccupationInner_smul_left,
    star_sum,star_mul,star_star,natPairNormalization_real,pairCoefficientNat_real]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

#print axioms fourCanonical_terms_flatMap
#print axioms fourCanonical_originalTerm_cross
#print axioms fourCanonical_column_pair_cross
end TorusLean.Shared.ThermalCoherentBosonRows
