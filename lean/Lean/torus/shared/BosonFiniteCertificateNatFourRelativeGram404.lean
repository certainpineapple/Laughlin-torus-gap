import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis404
import torus.shared.BosonFiniteCertificate404

/-! Degree-4 actual relative-family factorial Gram and its two-sided inverse.
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

def f404wordMetric : Fin 5 → ℕ := ![144, 12, 16, 4, 24]

def f404relativeGram : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(160/3), (-112/3);
    (-112/3), (232/3)]

def f404relativeGramInverse : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(29/1024), (7/512);
    (7/512), (5/256)]

def f404relativeFamily : Fin 2 → Core ℕ ℂ :=
  natFourColumnFamily f404basis b404relative

theorem f404_word_metric_check : ∀ a,
    natFourWordMetric (f404basis a)=f404wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f404basis a)=f404wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f404GramIntegerCoordinates : Matrix (Fin 5) (Fin 2) ℤ :=
  !![1, -1;
    -4, 4;
    3, 0;
    0, -6;
    0, 3]

private def f404GramIntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![480, -336;
    -336, 696]

theorem f404_relative_gram_check :
    b404relativeᵀ*natFourWordGram f404basis*b404relative=f404relativeGram := by
  have hG : natFourWordGram f404basis=Matrix.diagonal (fun a => (f404wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f404_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 3 f404GramIntegerCoordinates=b404relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 5, f404GramIntegerCoordinates a i*(f404wordMetric a : ℤ)*
      f404GramIntegerCoordinates a j)=f404GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => ∑ a : Fin 5, f404GramIntegerCoordinates a 0*
          (f404wordMetric a : ℤ)*f404GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 2) => f404GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => ∑ a : Fin 5, f404GramIntegerCoordinates a 1*
          (f404wordMetric a : ℤ)*f404GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 2) => f404GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (3*3) f404GramIntegerForm=f404relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 3 f404wordMetric
    f404GramIntegerCoordinates f404GramIntegerForm b404relative f404relativeGram hU hY hF

theorem f404_actual_relative_gram :
    natFamilyGram f404relativeFamily=complexify f404relativeGram := by
  rw [f404relativeFamily,natFourColumnFamily_gram f404basis f404_occupation_injective,
    f404_relative_gram_check]

theorem f404_relative_gram_inverse_right :
    f404relativeGram*f404relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f404_relative_gram_inverse_left :
    f404relativeGramInverse*f404relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f404_relative_gram_inverse_symmetric :
    f404relativeGramInverseᵀ=f404relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f404_word_metric_check
#print axioms f404_relative_gram_check
#print axioms f404_actual_relative_gram
#print axioms f404_relative_gram_inverse_right
#print axioms f404_relative_gram_inverse_left
#print axioms f404_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
