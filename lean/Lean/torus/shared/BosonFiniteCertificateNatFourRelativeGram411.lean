import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis411
import torus.shared.BosonFiniteCertificate411

/-! Degree-11 actual relative-family factorial Gram and its two-sided inverse.
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

def f411wordMetric : Fin 27 → ℕ := ![239500800, 7257600, 1451520, 483840, 241920, 172800, 725760, 80640, 30240, 17280, 28800, 40320, 8640, 5760, 8640, 6912, 241920, 20160, 8640, 5760, 5760, 1440, 2304, 1728, 5760, 1152, 2592]

def f411relativeGram : Matrix (Fin 4) (Fin 4) ℚ :=
  !![243200, (-798720/7), (-660480/7), (856320/7);
    (-798720/7), (7446528/35), (589824/5), (-6617088/35);
    (-660480/7), (589824/5), (4663296/35), (-7985664/35);
    (856320/7), (-6617088/35), (-7985664/35), (15778944/35)]

def f411relativeGramInverse : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(8611/1258291200), (433/301989888), (359/33554432), (157/37748736);
    (433/301989888), (5905/603979776), (-5825/603979776), (-265/226492416);
    (359/33554432), (-5825/603979776), (53105/603979776), (315/8388608);
    (157/37748736), (-265/226492416), (315/8388608), (185/9437184)]

def f411relativeFamily : Fin 4 → Core ℕ ℂ :=
  natFourColumnFamily f411basis b411relative

theorem f411_word_metric_check : ∀ a,
    natFourWordMetric (f411basis a)=f411wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f411basis a)=f411wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f411GramIntegerCoordinates : Matrix (Fin 27) (Fin 4) ℤ :=
  !![10, -12, -12, 21;
    -110, 132, 132, -231;
    350, -276, -204, 285;
    -750, 252, 180, -117;
    900, -72, -72, 0;
    -420, 0, 0, 0;
    200, -384, -456, 870;
    -900, 1728, 1296, -2214;
    2400, -1728, -1152, 936;
    -4200, 504, 504, 0;
    2520, 0, 0, 0;
    0, -2160, -720, 1458;
    0, 5040, 1008, -1260;
    0, -1512, -504, 0;
    0, -4032, 0, 252;
    0, 2520, 0, 0;
    0, 0, 504, -1134;
    0, 0, -2016, 4536;
    0, 0, 2016, -2016;
    0, 0, -1008, 0;
    0, 0, 2016, -6426;
    0, 0, -4032, 6048;
    0, 0, 2520, 0;
    0, 0, 0, -1260;
    0, 0, 0, 3402;
    0, 0, 0, -5670;
    0, 0, 0, 2520]

private def f411GramIntegerForm : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1544417280000, -724598784000, -599187456000, 776853504000;
    -724598784000, 1351098040320, 749123665920, -1200604446720;
    -599187456000, 749123665920, 846108426240, -1448918876160;
    776853504000, -1200604446720, -1448918876160, 2862931599360]

theorem f411_relative_gram_check :
    b411relativeᵀ*natFourWordGram f411basis*b411relative=f411relativeGram := by
  have hG : natFourWordGram f411basis=Matrix.diagonal (fun a => (f411wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f411_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 2520 f411GramIntegerCoordinates=b411relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 27, f411GramIntegerCoordinates a i*(f411wordMetric a : ℤ)*
      f411GramIntegerCoordinates a j)=f411GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 27, f411GramIntegerCoordinates a 0*
          (f411wordMetric a : ℤ)*f411GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f411GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 27, f411GramIntegerCoordinates a 1*
          (f411wordMetric a : ℤ)*f411GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f411GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 27, f411GramIntegerCoordinates a 2*
          (f411wordMetric a : ℤ)*f411GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f411GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => ∑ a : Fin 27, f411GramIntegerCoordinates a 3*
          (f411wordMetric a : ℤ)*f411GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 4) => f411GramIntegerForm 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (2520*2520) f411GramIntegerForm=f411relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 2520 f411wordMetric
    f411GramIntegerCoordinates f411GramIntegerForm b411relative f411relativeGram hU hY hF

theorem f411_actual_relative_gram :
    natFamilyGram f411relativeFamily=complexify f411relativeGram := by
  rw [f411relativeFamily,natFourColumnFamily_gram f411basis f411_occupation_injective,
    f411_relative_gram_check]

theorem f411_relative_gram_inverse_right :
    f411relativeGram*f411relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f411_relative_gram_inverse_left :
    f411relativeGramInverse*f411relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f411_relative_gram_inverse_symmetric :
    f411relativeGramInverseᵀ=f411relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f411_word_metric_check
#print axioms f411_relative_gram_check
#print axioms f411_actual_relative_gram
#print axioms f411_relative_gram_inverse_right
#print axioms f411_relative_gram_inverse_left
#print axioms f411_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
