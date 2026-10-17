import torus.shared.BosonFiniteCertificateNatFourCOMRelativeFamilyGram
import torus.shared.BosonFiniteCertificateCanonicalCompressionCore
import torus.shared.BosonFiniteCertificateCanonicalRowAssembly

/-! Uniform interfaces to the seventeen original relative form matrices.
The M entry is exactly the original COM average, already including its
2/(4^(n+1)n!) weights once. Rank coefficients retain both actual inverse Grams.
These definitions do not define any of the independently given source operators. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateRealization
open Matrix
open scoped BigOperators ComplexOrder

def natFourRelativeCOMMatrix (d : Fin 17) : Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ := by
  refine Fin.cases ?_ ?_ d
  · exact b400average
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact b401average
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact b402average
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact b403average
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact b404average
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact b405average
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact b406average
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact b407average
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact b408average
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact b409average
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact b410average
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact b411average
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact b412average
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact b413average
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact b414average
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact b415average
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact b416average
                                  · intro d
                                    exact Fin.elim0 d

def natFourRelativeS4Matrix (d : Fin 17) : Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ := by
  refine Fin.cases ?_ ?_ d
  · exact b400s
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact b401s
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact b402s
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact b403s
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact b404s
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact b405s
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact b406s
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact b407s
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact b408s
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact b409s
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact b410s
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact b411s
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact b412s
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact b413s
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact b414s
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact b415s
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact b416s
                                  · intro d
                                    exact Fin.elim0 d

def natFourRelativeHMatrix (d : Fin 17) : Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ := by
  refine Fin.cases ?_ ?_ d
  · exact b400h
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact b401h
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact b402h
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact b403h
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact b404h
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact b405h
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact b406h
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact b407h
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact b408h
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact b409h
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact b410h
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact b411h
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact b412h
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact b413h
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact b414h
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact b415h
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact b416h
                                  · intro d
                                    exact Fin.elim0 d

def natFourRelativeComparisonMatrix (d : Fin 17) : Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ := by
  refine Fin.cases ?_ ?_ d
  · exact b400comparison
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact b401comparison
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact b402comparison
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact b403comparison
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact b404comparison
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact b405comparison
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact b406comparison
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact b407comparison
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact b408comparison
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact b409comparison
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact b410comparison
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact b411comparison
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact b412comparison
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact b413comparison
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact b414comparison
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact b415comparison
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact b416comparison
                                  · intro d
                                    exact Fin.elim0 d

def natFourRelativeRankCoefficient (d : Fin 17) (E : Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ) :
    Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℂ :=
  inverseGramCoefficient (complexify (natFourRelativeGramInverse d)) (complexify E)

def natFourRelativeM4RankCoefficient (d : Fin 17) :
    Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℂ :=
  natFourRelativeRankCoefficient d (natFourRelativeCOMMatrix d)

def natFourRelativeS4RankCoefficient (d : Fin 17) :
    Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℂ :=
  natFourRelativeRankCoefficient d (natFourRelativeS4Matrix d)

def natFourRelativeHRankCoefficient (d : Fin 17) :
    Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℂ :=
  natFourRelativeRankCoefficient d (natFourRelativeHMatrix d)

def natFourRelativeComparisonRankCoefficient (d : Fin 17) :
    Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℂ :=
  natFourRelativeRankCoefficient d (natFourRelativeComparisonMatrix d)

theorem natFourRelativeComparisonMatrix_eq (d : Fin 17) :
    natFourRelativeComparisonMatrix d = alpha • natFourRelativeS4Matrix d -
      natFourRelativeCOMMatrix d + delta • natFourRelativeHMatrix d := by
  fin_cases d <;> rfl

theorem natFourRelativeComparisonMatrix_posSemidef (d : Fin 17) :
    (complexify (natFourRelativeComparisonMatrix d)).PosSemidef := by
  fin_cases d
  · exact b400_comparison_positive
  · exact b401_comparison_positive
  · exact b402_comparison_positive
  · exact b403_comparison_positive
  · exact b404_comparison_positive
  · exact b405_comparison_positive
  · exact b406_comparison_positive
  · exact b407_comparison_positive
  · exact b408_comparison_positive
  · exact b409_comparison_positive
  · exact b410_comparison_positive
  · exact b411_comparison_positive
  · exact b412_comparison_positive
  · exact b413_comparison_positive
  · exact b414_comparison_positive
  · exact b415_comparison_positive
  · exact b416_comparison_positive

theorem natFourRelativeComparisonRankCoefficient_posSemidef (d : Fin 17) :
    (natFourRelativeComparisonRankCoefficient d).PosSemidef :=
  natFour_inverseGramCoefficient_posSemidef (natFourRelativeGramInverse d)
    (complexify (natFourRelativeComparisonMatrix d))
    (natFourRelativeGramInverse_symmetric d) (natFourRelativeComparisonMatrix_posSemidef d)

theorem natFourRelativeComparisonRankCoefficient_eq (d : Fin 17) :
    natFourRelativeComparisonRankCoefficient d =
      (alpha : ℂ) • natFourRelativeS4RankCoefficient d - natFourRelativeM4RankCoefficient d +
        (delta : ℂ) • natFourRelativeHRankCoefficient d := by
  unfold natFourRelativeComparisonRankCoefficient natFourRelativeS4RankCoefficient
    natFourRelativeM4RankCoefficient natFourRelativeHRankCoefficient natFourRelativeRankCoefficient
  rw [natFourRelativeComparisonMatrix_eq]
  simp only [complexify_add_rect,complexify_sub_rect,complexify_smul_rat,
    inverseGramCoefficient,Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul]

#print axioms natFourRelativeComparisonMatrix_eq
#print axioms natFourRelativeComparisonMatrix_posSemidef
#print axioms natFourRelativeComparisonRankCoefficient_posSemidef
#print axioms natFourRelativeComparisonRankCoefficient_eq
end TorusLean.BosonFiniteCertificate
