import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis413
import torus.shared.BosonFiniteCertificate413

/-! Degree-13 actual relative-family factorial Gram and its two-sided inverse.
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

def f413wordMetric : Fin 39 → ℕ := ![37362124800, 958003200, 159667200, 43545600, 17418240, 9676800, 7257600, 79833600, 7257600, 2177280, 967680, 604800, 1036800, 2903040, 483840, 241920, 172800, 362880, 103680, 172800, 138240, 21772800, 1451520, 483840, 241920, 172800, 322560, 60480, 34560, 57600, 51840, 17280, 82944, 241920, 34560, 23040, 17280, 13824, 31104]

def f413relativeGram : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(102297600/11), (-219571200/77), (-199296000/77), (211415040/77), (159713280/77);
    (-219571200/77), (51168000/11), (190905600/77), (-337382400/77), (-35489280/11);
    (-199296000/77), (190905600/77), (217376000/77), (-303590400/77), (-286947840/77);
    (211415040/77), (-337382400/77), (-303590400/77), (2667024384/385), (2433251328/385);
    (159713280/77), (-35489280/11), (-286947840/77), (2433251328/385), (389446656/55)]

def f413relativeGramInverse : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(191933/1087163596800), (7/75497472), (9751/30198988800), (4067/28991029248), (511/14495514624);
    (7/75497472), (71/94371840), (11/117964800), (389/452984832), (-91/226492416);
    (9751/30198988800), (11/117964800), (5951/2516582400), (2459/2415919104), (343/1207959552);
    (4067/28991029248), (389/452984832), (2459/2415919104), (125855/57982058496), (-30485/28991029248);
    (511/14495514624), (-91/226492416), (343/1207959552), (-30485/28991029248), (5005/4831838208)]

def f413relativeFamily : Fin 5 → Core ℕ ℂ :=
  natFourColumnFamily f413basis b413relative

theorem f413_word_metric_check : ∀ a,
    natFourWordMetric (f413basis a)=f413wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f413basis a)=f413wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f413GramIntegerCoordinates : Matrix (Fin 39) (Fin 5) ℤ :=
  !![-30, 35, 35, -56, -56;
    390, -455, -455, 728, 728;
    -1620, 1230, 1010, -1440, -1176;
    4620, -1760, -1540, 1496, 836;
    -8250, 1375, 1375, -616, -220;
    8910, -495, -495, 0, 0;
    -3960, 0, 0, 0, 0;
    -720, 1500, 1720, -2928, -3192;
    3960, -8250, -6490, 11352, 10428;
    -13200, 12100, 9900, -12496, -7480;
    29700, -9900, -9900, 5544, 1980;
    -47520, 3960, 3960, 0, 0;
    27720, 0, 0, 0, 0;
    0, 11550, 3850, -11088, -8580;
    0, -34650, -8250, 26136, 12276;
    0, 29700, 9900, -12672, -3168;
    0, -13860, -4620, 0, 0;
    0, 26400, 0, -16896, -4224;
    0, -46200, 0, 18480, 1848;
    0, 27720, 0, 0, 0;
    0, 0, 0, -5544, 0;
    0, 0, -1980, 3168, 4752;
    0, 0, 9900, -15840, -23760;
    0, 0, -16500, 19008, 17424;
    0, 0, 19800, -9504, -4752;
    0, 0, -9240, 0, 0;
    0, 0, -9900, 21384, 40392;
    0, 0, 26400, -57024, -60192;
    0, 0, -46200, 33264, 16632;
    0, 0, 27720, 0, 0;
    0, 0, 0, 44352, 22176;
    0, 0, 0, -66528, -11088;
    0, 0, 0, 27720, 0;
    0, 0, 0, 0, -23760;
    0, 0, 0, 0, 55440;
    0, 0, 0, 0, -16632;
    0, 0, 0, 0, -44352;
    0, 0, 0, 0, 27720;
    0, 0, 0, 0, 0]

private def f413GramIntegerForm : Matrix (Fin 5) (Fin 5) ℤ :=
  !![7145937469440000, -2191144919040000, -1988814643200000, 2109752967168000, 1593810763776000;
    -2191144919040000, 3574309939200000, 1905085163520000, -3366806446080000, -2479082360832000;
    -1988814643200000, 1905085163520000, 2169238579200000, -3029589319680000, -2863509884928000;
    2109752967168000, -3366806446080000, -3029589319680000, 5322953946562560, 4856380330475520;
    1593810763776000, -2479082360832000, -2863509884928000, 4856380330475520, 5440912497377280]

theorem f413_relative_gram_check :
    b413relativeᵀ*natFourWordGram f413basis*b413relative=f413relativeGram := by
  have hG : natFourWordGram f413basis=Matrix.diagonal (fun a => (f413wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f413_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 27720 f413GramIntegerCoordinates=b413relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 39, f413GramIntegerCoordinates a i*(f413wordMetric a : ℤ)*
      f413GramIntegerCoordinates a j)=f413GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 39, f413GramIntegerCoordinates a 0*
          (f413wordMetric a : ℤ)*f413GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f413GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 39, f413GramIntegerCoordinates a 1*
          (f413wordMetric a : ℤ)*f413GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f413GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 39, f413GramIntegerCoordinates a 2*
          (f413wordMetric a : ℤ)*f413GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f413GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 39, f413GramIntegerCoordinates a 3*
          (f413wordMetric a : ℤ)*f413GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f413GramIntegerForm 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => ∑ a : Fin 39, f413GramIntegerCoordinates a 4*
          (f413wordMetric a : ℤ)*f413GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 5) => f413GramIntegerForm 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (27720*27720) f413GramIntegerForm=f413relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 27720 f413wordMetric
    f413GramIntegerCoordinates f413GramIntegerForm b413relative f413relativeGram hU hY hF

theorem f413_actual_relative_gram :
    natFamilyGram f413relativeFamily=complexify f413relativeGram := by
  rw [f413relativeFamily,natFourColumnFamily_gram f413basis f413_occupation_injective,
    f413_relative_gram_check]

theorem f413_relative_gram_inverse_right :
    f413relativeGram*f413relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f413_relative_gram_inverse_left :
    f413relativeGramInverse*f413relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f413_relative_gram_inverse_symmetric :
    f413relativeGramInverseᵀ=f413relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f413_word_metric_check
#print axioms f413_relative_gram_check
#print axioms f413_actual_relative_gram
#print axioms f413_relative_gram_inverse_right
#print axioms f413_relative_gram_inverse_left
#print axioms f413_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
