import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis407
import torus.shared.BosonFiniteCertificate407

/-! Degree-7 actual relative-family factorial Gram and its two-sided inverse.
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

def f407wordMetric : Fin 11 → ℕ := ![30240, 1440, 480, 288, 240, 48, 72, 48, 144, 24, 48]

def f407relativeGram : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(3168/5), (-3264/5);
    (-3264/5), (17536/15)]

def f407relativeGramInverse : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(137/36864), (17/8192);
    (17/8192), (33/16384)]

def f407relativeFamily : Fin 2 → Core ℕ ℂ :=
  natFourColumnFamily f407basis b407relative

theorem f407_word_metric_check : ∀ a,
    natFourWordMetric (f407basis a)=f407wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f407basis a)=f407wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f407GramIntegerCoordinates : Matrix (Fin 11) (Fin 2) ℤ :=
  !![3, -4;
    -21, 28;
    27, -16;
    -15, 0;
    36, -68;
    -90, 80;
    60, 0;
    0, -20;
    0, 60;
    0, -120;
    0, 60]

private def f407GramIntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2280960, -2350080;
    -2350080, 4208640]

theorem f407_relative_gram_check :
    b407relativeᵀ*natFourWordGram f407basis*b407relative=f407relativeGram := by
  have hG : natFourWordGram f407basis=Matrix.diagonal (fun a => (f407wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f407_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 60 f407GramIntegerCoordinates=b407relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 11, f407GramIntegerCoordinates a i*(f407wordMetric a : ℤ)*
      f407GramIntegerCoordinates a j)=f407GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => ∑ a : Fin 11, f407GramIntegerCoordinates a 0*
          (f407wordMetric a : ℤ)*f407GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 2) => f407GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => ∑ a : Fin 11, f407GramIntegerCoordinates a 1*
          (f407wordMetric a : ℤ)*f407GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 2) => f407GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (60*60) f407GramIntegerForm=f407relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 60 f407wordMetric
    f407GramIntegerCoordinates f407GramIntegerForm b407relative f407relativeGram hU hY hF

theorem f407_actual_relative_gram :
    natFamilyGram f407relativeFamily=complexify f407relativeGram := by
  rw [f407relativeFamily,natFourColumnFamily_gram f407basis f407_occupation_injective,
    f407_relative_gram_check]

theorem f407_relative_gram_inverse_right :
    f407relativeGram*f407relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f407_relative_gram_inverse_left :
    f407relativeGramInverse*f407relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f407_relative_gram_inverse_symmetric :
    f407relativeGramInverseᵀ=f407relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f407_word_metric_check
#print axioms f407_relative_gram_check
#print axioms f407_actual_relative_gram
#print axioms f407_relative_gram_inverse_right
#print axioms f407_relative_gram_inverse_left
#print axioms f407_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
