import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis412
import torus.shared.BosonFiniteCertificate412

/-! Degree-12 actual relative-family factorial Gram and its two-sided inverse.
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

def f412wordMetric : Fin 34 → ℕ := ![2874009600, 79833600, 14515200, 4354560, 1935360, 1209600, 2073600, 7257600, 725760, 241920, 120960, 86400, 322560, 60480, 34560, 57600, 51840, 17280, 82944, 2177280, 161280, 60480, 34560, 57600, 40320, 8640, 5760, 8640, 6912, 34560, 5760, 9216, 3456, 31104]

def f412relativeGram : Matrix (Fin 7) (Fin 7) ℚ :=
  !![(708480000/77), (-62208000/77), (42992640/77), (-60940800/77), (27786240/77), (24238080/77), (-38085120/77);
    (-62208000/77), (59251200/77), (-9400320/11), (38131200/77), (-42232320/77), (-36065280/77), (66977280/77);
    (42992640/77), (-9400320/11), (598385664/385), (-41725440/77), (327103488/385), (7483392/11), (-517957632/385);
    (-60940800/77), (38131200/77), (-41725440/77), (55379200/77), (-41640960/77), (-40514560/77), (73693440/77);
    (27786240/77), (-42232320/77), (327103488/385), (-41640960/77), (338609664/385), (320446464/385), (-652230144/385);
    (24238080/77), (-36065280/77), (7483392/11), (-40514560/77), (320446464/385), (50505728/55), (-712041984/385);
    (-38085120/77), (66977280/77), (-517957632/385), (73693440/77), (-652230144/385), (-712041984/385), (300177792/77)]

def f412relativeGramInverse : Matrix (Fin 7) (Fin 7) ℚ :=
  !![(22249/173946175488), (19213/120795955200), (2075/57982058496), (17017/120795955200), (1349/14495514624), (2177/19327352832), (1139/21743271936);
    (19213/120795955200), (142033/30198988800), (9245/4831838208), (-8183/6039797760), (515/1207959552), (6965/4831838208), (503/603979776);
    (2075/57982058496), (9245/4831838208), (428153/173946175488), (-2999/4831838208), (-14801/4831838208), (20393/19327352832), (-5461/21743271936);
    (17017/120795955200), (-8183/6039797760), (-2999/4831838208), (23429/6039797760), (797/402653184), (19201/4831838208), (1147/603979776);
    (1349/14495514624), (515/1207959552), (-14801/4831838208), (797/402653184), (56339/3623878656), (-18569/4831838208), (1997/603979776);
    (2177/19327352832), (6965/4831838208), (20393/19327352832), (19201/4831838208), (-18569/4831838208), (673057/19327352832), (33659/2415919104);
    (1139/21743271936), (503/603979776), (-5461/21743271936), (1147/603979776), (1997/603979776), (33659/2415919104), (6859/905969664)]

def f412relativeFamily : Fin 7 → Core ℕ ℂ :=
  natFourColumnFamily f412basis b412relative

theorem f412_word_metric_check : ∀ a,
    natFourWordMetric (f412basis a)=f412wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f412basis a)=f412wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f412GramIntegerCoordinates : Matrix (Fin 34) (Fin 7) ℤ :=
  !![15, -15, 21, -15, 21, 21, -42;
    -180, 180, -252, 180, -252, -252, 504;
    990, -495, 594, -440, 429, 374, -693;
    -3300, 825, -660, 825, -363, -264, 330;
    7425, -825, 297, -825, 99, 99, 0;
    -11880, 330, 0, 330, 0, 0, 0;
    6930, 0, 0, 0, 0, 0, 0;
    0, -495, 792, -550, 957, 1012, -2079;
    0, 2475, -3960, 1925, -3201, -2948, 5940;
    0, -4125, 4752, -4125, 2871, 1980, -2970;
    0, 4950, -2376, 4950, -792, -792, 0;
    0, -2310, 0, -2310, 0, 0, 0;
    0, -2475, 5346, 0, 2673, 1980, -4455;
    0, 6600, -14256, 0, -5148, -2112, 4752;
    0, -11550, 8316, 0, 1386, 924, 0;
    0, 6930, 0, 0, 0, 0, 0;
    0, 0, 11088, 0, 2772, 0, -1386;
    0, 0, -16632, 0, -1386, 0, 0;
    0, 0, 6930, 0, 0, 0, 0;
    0, 0, 0, 550, -1056, -1408, 2970;
    0, 0, 0, -2475, 4752, 6336, -13365;
    0, 0, 0, 6600, -4752, -4224, 7128;
    0, 0, 0, -11550, 1386, 1848, 0;
    0, 0, 0, 6930, 0, 0, 0;
    0, 0, 0, 0, -5940, -9504, 21384;
    0, 0, 0, 0, 13860, 11088, -24948;
    0, 0, 0, 0, -4158, -5544, 0;
    0, 0, 0, 0, -11088, 0, 8316;
    0, 0, 0, 0, 6930, 0, 0;
    0, 0, 0, 0, 0, 5544, -12474;
    0, 0, 0, 0, 0, -11088, 24948;
    0, 0, 0, 0, 0, 6930, 0;
    0, 0, 0, 0, 0, 0, -20790;
    0, 0, 0, 0, 0, 0, 6930]

private def f412GramIntegerForm : Matrix (Fin 7) (Fin 7) ℤ :=
  !![441878976000000, -38799129600000, 26814509568000, -38008776960000, 17330277888000, 15117290496000, -23753689344000;
    -38799129600000, 36954973440000, -41040857088000, 23782429440000, -26340297984000, -22493915136000, 41773729536000;
    26814509568000, -41040857088000, 74642627727360, -26024156928000, 40802889093120, 32671741132800, -64610035015680;
    -38008776960000, 23782429440000, -26024156928000, 34540007040000, -25971466752000, -25268931072000, 45962598528000;
    17330277888000, -26340297984000, 40802889093120, -25971466752000, 42238169487360, 39972491919360, -81359188162560;
    15117290496000, -22493915136000, 32671741132800, -25268931072000, 39972491919360, 44100591575040, -88820117084160;
    -23753689344000, 41773729536000, -64610035015680, 45962598528000, -81359188162560, -88820117084160, 187220888870400]

theorem f412_relative_gram_check :
    b412relativeᵀ*natFourWordGram f412basis*b412relative=f412relativeGram := by
  have hG : natFourWordGram f412basis=Matrix.diagonal (fun a => (f412wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f412_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 6930 f412GramIntegerCoordinates=b412relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 34, f412GramIntegerCoordinates a i*(f412wordMetric a : ℤ)*
      f412GramIntegerCoordinates a j)=f412GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 34, f412GramIntegerCoordinates a 0*
          (f412wordMetric a : ℤ)*f412GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f412GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 34, f412GramIntegerCoordinates a 1*
          (f412wordMetric a : ℤ)*f412GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f412GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 34, f412GramIntegerCoordinates a 2*
          (f412wordMetric a : ℤ)*f412GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f412GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 34, f412GramIntegerCoordinates a 3*
          (f412wordMetric a : ℤ)*f412GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f412GramIntegerForm 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 34, f412GramIntegerCoordinates a 4*
          (f412wordMetric a : ℤ)*f412GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f412GramIntegerForm 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 34, f412GramIntegerCoordinates a 5*
          (f412wordMetric a : ℤ)*f412GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f412GramIntegerForm 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 34, f412GramIntegerCoordinates a 6*
          (f412wordMetric a : ℤ)*f412GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f412GramIntegerForm 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (6930*6930) f412GramIntegerForm=f412relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 6930 f412wordMetric
    f412GramIntegerCoordinates f412GramIntegerForm b412relative f412relativeGram hU hY hF

theorem f412_actual_relative_gram :
    natFamilyGram f412relativeFamily=complexify f412relativeGram := by
  rw [f412relativeFamily,natFourColumnFamily_gram f412basis f412_occupation_injective,
    f412_relative_gram_check]

theorem f412_relative_gram_inverse_right :
    f412relativeGram*f412relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f412_relative_gram_inverse_left :
    f412relativeGramInverse*f412relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f412_relative_gram_inverse_symmetric :
    f412relativeGramInverseᵀ=f412relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f412_word_metric_check
#print axioms f412_relative_gram_check
#print axioms f412_actual_relative_gram
#print axioms f412_relative_gram_inverse_right
#print axioms f412_relative_gram_inverse_left
#print axioms f412_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
