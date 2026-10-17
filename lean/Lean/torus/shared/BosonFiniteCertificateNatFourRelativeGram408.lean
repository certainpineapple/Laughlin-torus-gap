import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis408
import torus.shared.BosonFiniteCertificate408

/-! Degree-8 actual relative-family factorial Gram and its two-sided inverse.
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

def f408wordMetric : Fin 15 → ℕ := ![241920, 10080, 2880, 1440, 2304, 1440, 240, 144, 192, 144, 720, 96, 144, 48, 384]

def f408relativeGram : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(59904/7), (-11520/7), (-49536/35), (63744/35);
    (-11520/7), (17568/7), (59616/35), (-104064/35);
    (-49536/35), (59616/35), (15552/7), (-121536/35);
    (63744/35), (-104064/35), (-121536/35), (712064/105)]

def f408relativeGramInverse : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(585/4194304), (21/262144), (281/2359296), (123/2097152);
    (21/262144), (137/147456), (-43/147456), (31/131072);
    (281/2359296), (-43/147456), (41/16384), (147/131072);
    (123/2097152), (31/131072), (147/131072), (849/1048576)]

def f408relativeFamily : Fin 4 → Core ℕ ℂ :=
  natFourColumnFamily f408basis b408relative

theorem f408_word_metric_check : ∀ a,
    natFourWordMetric (f408basis a)=f408wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f408basis a)=f408wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f408GramIntegerCoordinates : Matrix (Fin 15) (Fin 4) ℤ :=
  !![6, -6, -6, 10;
    -48, 48, 48, -80;
    168, -63, -42, 56;
    -336, 21, 21, 0;
    210, 0, 0, 0;
    0, -105, -126, 224;
    0, 315, 189, -336;
    0, -105, -105, 0;
    0, -315, 0, 140;
    0, 210, 0, 0;
    0, 0, 126, -224;
    0, 0, -315, 560;
    0, 0, 210, 0;
    0, 0, 0, -560;
    0, 0, 0, 210]

private def f408GramIntegerForm : Matrix (Fin 4) (Fin 4) ℤ :=
  !![377395200, -72576000, -62415360, 80317440;
    -72576000, 110678400, 75116160, -131120640;
    -62415360, 75116160, 97977600, -153135360;
    80317440, -131120640, -153135360, 299066880]

theorem f408_relative_gram_check :
    b408relativeᵀ*natFourWordGram f408basis*b408relative=f408relativeGram := by
  have hG : natFourWordGram f408basis=Matrix.diagonal (fun a => (f408wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f408_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 210 f408GramIntegerCoordinates=b408relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 15, f408GramIntegerCoordinates a i*(f408wordMetric a : ℤ)*
      f408GramIntegerCoordinates a j)=f408GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 15, f408GramIntegerCoordinates a 0*
          (f408wordMetric a : ℤ)*f408GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f408GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 15, f408GramIntegerCoordinates a 1*
          (f408wordMetric a : ℤ)*f408GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f408GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 15, f408GramIntegerCoordinates a 2*
          (f408wordMetric a : ℤ)*f408GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f408GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 15, f408GramIntegerCoordinates a 3*
          (f408wordMetric a : ℤ)*f408GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f408GramIntegerForm 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (210*210) f408GramIntegerForm=f408relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 210 f408wordMetric
    f408GramIntegerCoordinates f408GramIntegerForm b408relative f408relativeGram hU hY hF

theorem f408_actual_relative_gram :
    natFamilyGram f408relativeFamily=complexify f408relativeGram := by
  rw [f408relativeFamily,natFourColumnFamily_gram f408basis f408_occupation_injective,
    f408_relative_gram_check]

theorem f408_relative_gram_inverse_right :
    f408relativeGram*f408relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f408_relative_gram_inverse_left :
    f408relativeGramInverse*f408relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f408_relative_gram_inverse_symmetric :
    f408relativeGramInverseᵀ=f408relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f408_word_metric_check
#print axioms f408_relative_gram_check
#print axioms f408_actual_relative_gram
#print axioms f408_relative_gram_inverse_right
#print axioms f408_relative_gram_inverse_left
#print axioms f408_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
