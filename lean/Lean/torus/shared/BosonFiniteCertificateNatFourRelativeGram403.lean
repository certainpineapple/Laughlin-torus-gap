import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis403
import torus.shared.BosonFiniteCertificate403

/-! Degree-3 actual relative-family factorial Gram and its two-sided inverse.
The metric is checked on the independently defined Nat occupation words;
F is checked as Uᵀ G U. J is used on both sides of every rank coefficient. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

def f403wordMetric : Fin 3 → ℕ := ![36, 4, 6]

def f403relativeGram : Matrix (Fin 1) (Fin 1) ℚ :=
  !![24]

def f403relativeGramInverse : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/24)]

def f403relativeFamily : Fin 1 → Core ℕ ℂ :=
  natFourColumnFamily f403basis b403relative

theorem f403_word_metric_check : ∀ a,
    natFourWordMetric (f403basis a)=f403wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f403basis a)=f403wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f403GramIntegerCoordinates : Matrix (Fin 3) (Fin 1) ℤ :=
  !![1;
    -3;
    2]

private def f403GramIntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![96]

theorem f403_relative_gram_check :
    b403relativeᵀ*natFourWordGram f403basis*b403relative=f403relativeGram := by
  have hG : natFourWordGram f403basis=Matrix.diagonal (fun a => (f403wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f403_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 2 f403GramIntegerCoordinates=b403relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 3, f403GramIntegerCoordinates a i*(f403wordMetric a : ℤ)*
      f403GramIntegerCoordinates a j)=f403GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => ∑ a : Fin 3, f403GramIntegerCoordinates a 0*
          (f403wordMetric a : ℤ)*f403GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 1) => f403GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (2*2) f403GramIntegerForm=f403relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 2 f403wordMetric
    f403GramIntegerCoordinates f403GramIntegerForm b403relative f403relativeGram hU hY hF

theorem f403_actual_relative_gram :
    natFamilyGram f403relativeFamily=complexify f403relativeGram := by
  rw [f403relativeFamily,natFourColumnFamily_gram f403basis f403_occupation_injective,
    f403_relative_gram_check]

theorem f403_relative_gram_inverse_right :
    f403relativeGram*f403relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f403_relative_gram_inverse_left :
    f403relativeGramInverse*f403relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f403_relative_gram_inverse_symmetric :
    f403relativeGramInverseᵀ=f403relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f403_word_metric_check
#print axioms f403_relative_gram_check
#print axioms f403_actual_relative_gram
#print axioms f403_relative_gram_inverse_right
#print axioms f403_relative_gram_inverse_left
#print axioms f403_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
