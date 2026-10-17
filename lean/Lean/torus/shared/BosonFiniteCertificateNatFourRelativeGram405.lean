import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis405
import torus.shared.BosonFiniteCertificate405

/-! Degree-5 actual relative-family factorial Gram and its two-sided inverse.
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

def f405wordMetric : Fin 6 → ℕ := ![720, 48, 24, 12, 8, 12]

def f405relativeGram : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(256/3)]

def f405relativeGramInverse : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(3/256)]

def f405relativeFamily : Fin 1 → Core ℕ ℂ :=
  natFourColumnFamily f405basis b405relative

theorem f405_word_metric_check : ∀ a,
    natFourWordMetric (f405basis a)=f405wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f405basis a)=f405wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f405GramIntegerCoordinates : Matrix (Fin 6) (Fin 1) ℤ :=
  !![-1;
    5;
    -2;
    -8;
    6;
    0]

private def f405GramIntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![3072]

theorem f405_relative_gram_check :
    b405relativeᵀ*natFourWordGram f405basis*b405relative=f405relativeGram := by
  have hG : natFourWordGram f405basis=Matrix.diagonal (fun a => (f405wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f405_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 6 f405GramIntegerCoordinates=b405relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 6, f405GramIntegerCoordinates a i*(f405wordMetric a : ℤ)*
      f405GramIntegerCoordinates a j)=f405GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => ∑ a : Fin 6, f405GramIntegerCoordinates a 0*
          (f405wordMetric a : ℤ)*f405GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 1) => f405GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (6*6) f405GramIntegerForm=f405relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 6 f405wordMetric
    f405GramIntegerCoordinates f405GramIntegerForm b405relative f405relativeGram hU hY hF

theorem f405_actual_relative_gram :
    natFamilyGram f405relativeFamily=complexify f405relativeGram := by
  rw [f405relativeFamily,natFourColumnFamily_gram f405basis f405_occupation_injective,
    f405_relative_gram_check]

theorem f405_relative_gram_inverse_right :
    f405relativeGram*f405relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f405_relative_gram_inverse_left :
    f405relativeGramInverse*f405relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f405_relative_gram_inverse_symmetric :
    f405relativeGramInverseᵀ=f405relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f405_word_metric_check
#print axioms f405_relative_gram_check
#print axioms f405_actual_relative_gram
#print axioms f405_relative_gram_inverse_right
#print axioms f405_relative_gram_inverse_left
#print axioms f405_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
