import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis409
import torus.shared.BosonFiniteCertificate409

/-! Degree-9 actual relative-family factorial Gram and its two-sided inverse.
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

def f409wordMetric : Fin 18 → ℕ := ![2177280, 80640, 20160, 8640, 5760, 10080, 1440, 720, 1152, 960, 288, 1296, 4320, 480, 288, 192, 144, 288]

def f409relativeGram : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(331776/35), (-269568/35), (-205056/35);
    (-269568/35), (94608/7), (58320/7);
    (-205056/35), (58320/7), (70416/7)]

def f409relativeGramInverse : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(325/1572864), (35/393216), (55/1179648);
    (35/393216), (503/2654208), (-31/294912);
    (55/1179648), (-31/294912), (7/32768)]

def f409relativeFamily : Fin 3 → Core ℕ ℂ :=
  natFourColumnFamily f409basis b409relative

theorem f409_word_metric_check : ∀ a,
    natFourWordMetric (f409basis a)=f409wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f409basis a)=f409wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f409GramIntegerCoordinates : Matrix (Fin 18) (Fin 3) ℤ :=
  !![-4, 5, 5;
    36, -45, -45;
    -80, 72, 44;
    112, -42, -14;
    -56, 0, 0;
    -64, 108, 136;
    224, -378, -266;
    -448, 252, 84;
    280, 0, 0;
    0, 378, 126;
    0, -630, -70;
    0, 280, 0;
    0, 0, -140;
    0, 0, 420;
    0, 0, -140;
    0, 0, -420;
    0, 0, 280;
    0, 0, 0]

private def f409GramIntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![743178240, -603832320, -459325440;
    -603832320, 1059609600, 653184000;
    -459325440, 653184000, 788659200]

theorem f409_relative_gram_check :
    b409relativeᵀ*natFourWordGram f409basis*b409relative=f409relativeGram := by
  have hG : natFourWordGram f409basis=Matrix.diagonal (fun a => (f409wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f409_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 280 f409GramIntegerCoordinates=b409relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 18, f409GramIntegerCoordinates a i*(f409wordMetric a : ℤ)*
      f409GramIntegerCoordinates a j)=f409GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => ∑ a : Fin 18, f409GramIntegerCoordinates a 0*
          (f409wordMetric a : ℤ)*f409GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 3) => f409GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => ∑ a : Fin 18, f409GramIntegerCoordinates a 1*
          (f409wordMetric a : ℤ)*f409GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 3) => f409GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => ∑ a : Fin 18, f409GramIntegerCoordinates a 2*
          (f409wordMetric a : ℤ)*f409GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 3) => f409GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (280*280) f409GramIntegerForm=f409relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 280 f409wordMetric
    f409GramIntegerCoordinates f409GramIntegerForm b409relative f409relativeGram hU hY hF

theorem f409_actual_relative_gram :
    natFamilyGram f409relativeFamily=complexify f409relativeGram := by
  rw [f409relativeFamily,natFourColumnFamily_gram f409basis f409_occupation_injective,
    f409_relative_gram_check]

theorem f409_relative_gram_inverse_right :
    f409relativeGram*f409relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f409_relative_gram_inverse_left :
    f409relativeGramInverse*f409relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f409_relative_gram_inverse_symmetric :
    f409relativeGramInverseᵀ=f409relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f409_word_metric_check
#print axioms f409_relative_gram_check
#print axioms f409_actual_relative_gram
#print axioms f409_relative_gram_inverse_right
#print axioms f409_relative_gram_inverse_left
#print axioms f409_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
