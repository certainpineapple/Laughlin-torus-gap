import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis402
import torus.shared.BosonFiniteCertificate402

/-! Degree-2 actual relative-family factorial Gram and its two-sided inverse.
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

def f402wordMetric : Fin 2 → ℕ := ![12, 4]

def f402relativeGram : Matrix (Fin 1) (Fin 1) ℚ :=
  !![16]

def f402relativeGramInverse : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1/16)]

def f402relativeFamily : Fin 1 → Core ℕ ℂ :=
  natFourColumnFamily f402basis b402relative

theorem f402_word_metric_check : ∀ a,
    natFourWordMetric (f402basis a)=f402wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f402basis a)=f402wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f402GramIntegerCoordinates : Matrix (Fin 2) (Fin 1) ℤ :=
  !![-1;
    1]

private def f402GramIntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![16]

theorem f402_relative_gram_check :
    b402relativeᵀ*natFourWordGram f402basis*b402relative=f402relativeGram := by
  have hG : natFourWordGram f402basis=Matrix.diagonal (fun a => (f402wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f402_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 1 f402GramIntegerCoordinates=b402relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 2, f402GramIntegerCoordinates a i*(f402wordMetric a : ℤ)*
      f402GramIntegerCoordinates a j)=f402GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => ∑ a : Fin 2, f402GramIntegerCoordinates a 0*
          (f402wordMetric a : ℤ)*f402GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 1) => f402GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (1*1) f402GramIntegerForm=f402relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 1 f402wordMetric
    f402GramIntegerCoordinates f402GramIntegerForm b402relative f402relativeGram hU hY hF

theorem f402_actual_relative_gram :
    natFamilyGram f402relativeFamily=complexify f402relativeGram := by
  rw [f402relativeFamily,natFourColumnFamily_gram f402basis f402_occupation_injective,
    f402_relative_gram_check]

theorem f402_relative_gram_inverse_right :
    f402relativeGram*f402relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f402_relative_gram_inverse_left :
    f402relativeGramInverse*f402relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f402_relative_gram_inverse_symmetric :
    f402relativeGramInverseᵀ=f402relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f402_word_metric_check
#print axioms f402_relative_gram_check
#print axioms f402_actual_relative_gram
#print axioms f402_relative_gram_inverse_right
#print axioms f402_relative_gram_inverse_left
#print axioms f402_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
