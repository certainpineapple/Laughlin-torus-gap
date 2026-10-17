import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis410
import torus.shared.BosonFiniteCertificate410

/-! Degree-10 actual relative-family factorial Gram and its two-sided inverse.
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

def f410wordMetric : Fin 23 → ℕ := ![21772800, 725760, 161280, 60480, 34560, 57600, 80640, 10080, 4320, 2880, 5760, 1440, 2304, 1728, 30240, 2880, 1440, 2304, 960, 288, 1296, 1152, 576]

def f410relativeGram : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(1644800/7), (-193280/7), (-181760/7), 22080, (122880/7);
    (-193280/7), (1192192/35), (779776/35), (-169152/5), (-1033728/35);
    (-181760/7), (779776/35), (151552/5), (-246144/7), (-1181184/35);
    22080, (-169152/5), (-246144/7), (2046096/35), (2017152/35);
    (122880/7), (-1033728/35), (-1181184/35), (2017152/35), (2301696/35)]

def f410relativeGramInverse : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(38023/7549747200), (147/33554432), (1831/301989888), (83/18874368), (-1/8388608);
    (147/33554432), (25127/301989888), (-2477/301989888), (1391/18874368), (-2461/75497472);
    (1831/301989888), (-2477/301989888), (4023/33554432), (1339/18874368), (-449/75497472);
    (83/18874368), (1391/18874368), (1339/18874368), (869/3538944), (-77/524288);
    (-1/8388608), (-2461/75497472), (-449/75497472), (-77/524288), (2383/18874368)]

def f410relativeFamily : Fin 5 → Core ℕ ℂ :=
  natFourColumnFamily f410basis b410relative

theorem f410_word_metric_check : ∀ a,
    natFourWordMetric (f410basis a)=f410wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f410basis a)=f410wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f410GramIntegerCoordinates : Matrix (Fin 23) (Fin 5) ℤ :=
  !![-10, 10, 10, -15, -15;
    100, -100, -100, 150, 150;
    -450, 198, 162, -189, -153;
    1200, -192, -192, 99, 36;
    -2100, 84, 84, 0, 0;
    1260, 0, 0, 0, 0;
    0, 252, 288, -486, -522;
    0, -1008, -720, 1215, 1116;
    0, 1008, 1008, -693, -252;
    0, -504, -504, 0, 0;
    0, 1008, 0, -756, -630;
    0, -2016, 0, 945, 252;
    0, 1260, 0, 0, 0;
    0, 0, 0, -315, 0;
    0, 0, -288, 486, 648;
    0, 0, 1008, -1701, -2268;
    0, 0, -2016, 1134, 504;
    0, 0, 1260, 0, 0;
    0, 0, 0, 1701, 3024;
    0, 0, 0, -2835, -1260;
    0, 0, 0, 1260, 0;
    0, 0, 0, 0, -1890;
    0, 0, 0, 0, 1260]

private def f410GramIntegerForm : Matrix (Fin 5) (Fin 5) ℤ :=
  !![373040640000, -43835904000, -41223168000, 35054208000, 27869184000;
    -43835904000, 54077829120, 35370639360, -53709143040, -46889902080;
    -41223168000, 35370639360, 48120791040, -55825459200, -53578506240;
    35054208000, -53709143040, -55825459200, 92810914560, 91498014720;
    27869184000, -46889902080, -53578506240, 91498014720, 104404930560]

theorem f410_relative_gram_check :
    b410relativeᵀ*natFourWordGram f410basis*b410relative=f410relativeGram := by
  have hG : natFourWordGram f410basis=Matrix.diagonal (fun a => (f410wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f410_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 1260 f410GramIntegerCoordinates=b410relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 23, f410GramIntegerCoordinates a i*(f410wordMetric a : ℤ)*
      f410GramIntegerCoordinates a j)=f410GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 23, f410GramIntegerCoordinates a 0*
          (f410wordMetric a : ℤ)*f410GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f410GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 23, f410GramIntegerCoordinates a 1*
          (f410wordMetric a : ℤ)*f410GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f410GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 23, f410GramIntegerCoordinates a 2*
          (f410wordMetric a : ℤ)*f410GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f410GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 23, f410GramIntegerCoordinates a 3*
          (f410wordMetric a : ℤ)*f410GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f410GramIntegerForm 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 23, f410GramIntegerCoordinates a 4*
          (f410wordMetric a : ℤ)*f410GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f410GramIntegerForm 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (1260*1260) f410GramIntegerForm=f410relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 1260 f410wordMetric
    f410GramIntegerCoordinates f410GramIntegerForm b410relative f410relativeGram hU hY hF

theorem f410_actual_relative_gram :
    natFamilyGram f410relativeFamily=complexify f410relativeGram := by
  rw [f410relativeFamily,natFourColumnFamily_gram f410basis f410_occupation_injective,
    f410_relative_gram_check]

theorem f410_relative_gram_inverse_right :
    f410relativeGram*f410relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f410_relative_gram_inverse_left :
    f410relativeGramInverse*f410relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f410_relative_gram_inverse_symmetric :
    f410relativeGramInverseᵀ=f410relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f410_word_metric_check
#print axioms f410_relative_gram_check
#print axioms f410_actual_relative_gram
#print axioms f410_relative_gram_inverse_right
#print axioms f410_relative_gram_inverse_left
#print axioms f410_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
