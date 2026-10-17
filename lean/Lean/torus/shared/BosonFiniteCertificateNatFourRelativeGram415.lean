import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis415
import torus.shared.BosonFiniteCertificate415

/-! Degree-15 actual relative-family factorial Gram and its two-sided inverse.
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

def f415wordMetric : Fin 54 → ℕ := ![7846046208000, 174356582400, 24908083200, 5748019200, 1916006400, 870912000, 522547200, 406425600, 12454041600, 958003200, 239500800, 87091200, 43545600, 29030400, 50803200, 319334400, 43545600, 17418240, 9676800, 7257600, 26127360, 5806080, 3628800, 6220800, 5806080, 2073600, 10368000, 2874009600, 159667200, 43545600, 17418240, 9676800, 7257600, 29030400, 4354560, 1935360, 1209600, 2073600, 2903040, 725760, 518400, 829440, 691200, 17418240, 1935360, 967680, 691200, 725760, 207360, 345600, 276480, 933120, 207360, 497664]

def f415relativeGram : Matrix (Fin 7) (Fin 7) ℚ :=
  !![(69600384000/143), (-16140902400/143), (14587776000/143), (-15511910400/143), (9891302400/143), (8234956800/143), (-11991490560/143);
    (-16140902400/143), (149183078400/1001), (-28532736000/143), (78879744000/1001), (-16168550400/143), (-80184729600/1001), (12647301120/91);
    (14587776000/143), (-28532736000/143), (52189056000/143), (-99899136000/1001), (186090624000/1001), (122996736000/1001), (-31828377600/143);
    (-15511910400/143), (78879744000/1001), (-99899136000/1001), (93867724800/1001), (-95202662400/1001), (-12897792000/143), (159564349440/1001);
    (9891302400/143), (-16168550400/143), (186090624000/1001), (-95202662400/1001), (166218470400/1001), (141686784000/1001), (-276089241600/1001);
    (8234956800/143), (-80184729600/1001), (122996736000/1001), (-12897792000/143), (141686784000/1001), (152503449600/1001), (-311116308480/1001);
    (-11991490560/143), (12647301120/91), (-31828377600/143), (159564349440/1001), (-276089241600/1001), (-311116308480/1001), (3335115866112/5005)]

def f415relativeGramInverse : Matrix (Fin 7) (Fin 7) ℚ :=
  !![(314189/94704028876800), (85193/34789235097600), (7667/11596411699200), (218431/34789235097600), (4279/3865470566400), (2551/386547056640), (6017/2783138807808);
    (85193/34789235097600), (2433053/69578470195200), (360143/23192823398400), (-760949/69578470195200), (7637/4638564679680), (-721/3865470566400), (7861/5566277615616);
    (7667/11596411699200), (360143/23192823398400), (5405873/347892350976000), (-36701/7730941132800), (-395207/23192823398400), (115421/11596411699200), (4229/5566277615616);
    (218431/34789235097600), (-760949/69578470195200), (-36701/7730941132800), (60935/927712935936), (41951/23192823398400), (431753/3865470566400), (214963/5566277615616);
    (4279/3865470566400), (7637/4638564679680), (-395207/23192823398400), (41951/23192823398400), (547333/7730941132800), (-290599/3865470566400), (-7477/618475290624);
    (2551/386547056640), (-721/3865470566400), (115421/11596411699200), (431753/3865470566400), (-290599/3865470566400), (896509/1932735283200), (150949/927712935936);
    (6017/2783138807808), (7861/5566277615616), (4229/5566277615616), (214963/5566277615616), (-7477/618475290624), (150949/927712935936), (705605/11132555231232)]

def f415relativeFamily : Fin 7 → Core ℕ ℂ :=
  natFourColumnFamily f415basis b415relative

theorem f415_word_metric_check : ∀ a,
    natFourWordMetric (f415basis a)=f415wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f415basis a)=f415wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f415GramIntegerCoordinates : Matrix (Fin 54) (Fin 7) ℤ :=
  !![105, -120, 180, -120, 180, 180, -360;
    -1575, 1800, -2700, 1800, -2700, -2700, 5400;
    8085, -6120, 8400, -5340, 6580, 5670, -10248;
    -28665, 12480, -13650, 11700, -8970, -6630, 8736;
    66885, -16380, 11700, -16380, 5980, 4550, -2808;
    -105105, 12870, -4290, 12870, -1430, -1430, 0;
    105105, -4290, 0, -4290, 0, 0, 0;
    -45045, 0, 0, 0, 0, 0, 0;
    2940, -6480, 10500, -7260, 12320, 13230, -27552;
    -19110, 42120, -68250, 34320, -58630, -53820, 107016;
    76440, -84240, 117000, -74880, 83720, 61360, -93600;
    -210210, 115830, -107250, 115830, -58630, -42900, 30888;
    420420, -102960, 42900, -102960, 14300, 14300, 0;
    -630630, 38610, 0, 38610, 0, 0, 0;
    360360, 0, 0, 0, 0, 0, 0;
    0, -63180, 117000, -21060, 70200, 51090, -106704;
    0, 231660, -429000, 60060, -211640, -105820, 192192;
    0, -321750, 429000, -107250, 157300, 71500, -65208;
    0, 347490, -193050, 115830, -38610, -25740, 0;
    0, -154440, 0, -51480, 0, 0, 0;
    0, -171600, 429000, 0, 171600, 42900, -89232;
    0, 386100, -965250, 0, -278850, -42900, 61776;
    0, -617760, 514800, 0, 68640, 17160, 0;
    0, 360360, 0, 0, 0, 0, 0;
    0, 0, 643500, 0, 128700, 0, -10296;
    0, 0, -900900, 0, -60060, 0, 0;
    0, 0, 360360, 0, 0, 0, 0;
    0, 0, 0, 8580, -14300, -21450, 48048;
    0, 0, 0, -51480, 85800, 128700, -288288;
    0, 0, 0, 120120, -131560, -145860, 260832;
    0, 0, 0, -214500, 100100, 107250, -89232;
    0, 0, 0, 231660, -25740, -38610, 0;
    0, 0, 0, -102960, 0, 0, 0;
    0, 0, 0, 51480, -137280, -244530, 597168;
    0, 0, 0, -171600, 457600, 514800, -1125696;
    0, 0, 0, 386100, -386100, -386100, 401544;
    0, 0, 0, -617760, 102960, 154440, 0;
    0, 0, 0, 360360, 0, 0, 0;
    0, 0, 0, 0, -429000, -214500, 555984;
    0, 0, 0, 0, 858000, 257400, -411840;
    0, 0, 0, 0, -240240, -120120, 0;
    0, 0, 0, 0, -600600, 0, 72072;
    0, 0, 0, 0, 360360, 0, 0;
    0, 0, 0, 0, 0, 150150, -432432;
    0, 0, 0, 0, 0, -450450, 1297296;
    0, 0, 0, 0, 0, 386100, -494208;
    0, 0, 0, 0, 0, -180180, 0;
    0, 0, 0, 0, 0, 343200, -1400256;
    0, 0, 0, 0, 0, -600600, 1153152;
    0, 0, 0, 0, 0, 360360, 0;
    0, 0, 0, 0, 0, 0, -216216;
    0, 0, 0, 0, 0, 0, 576576;
    0, 0, 0, 0, 0, 0, -864864;
    0, 0, 0, 0, 0, 0, 360360]

private def f415GramIntegerForm : Matrix (Fin 7) (Fin 7) ℤ :=
  !![63204609833164800000, -14657669683937280000, 13247264417587200000, -14086477519994880000, 8982362926817280000, 7478223561768960000, -10889558916268032000;
    -14657669683937280000, 19353461087600640000, -25910782997299200000, 10233037637222400000, -14682777031802880000, -10402332897116160000, 18048022469148672000;
    13247264417587200000, -25910782997299200000, 47393257514803200000, -12959874953625600000, 24141462215270400000, 15956317362585600000, -28903578862878720000;
    -14086477519994880000, 10233037637222400000, -12959874953625600000, 12177422391214080000, -12350603312087040000, -11712577779302400000, 20700219227111424000;
    8982362926817280000, -14682777031802880000, 24141462215270400000, -12350603312087040000, 21563455677603840000, 18380969813606400000, -35816946877071360000;
    7478223561768960000, -10402332897116160000, 15956317362585600000, -11712577779302400000, 18380969813606400000, 19784211515228160000, -40360994252587008000;
    -10889558916268032000, 18048022469148672000, -28903578862878720000, 20700219227111424000, -35816946877071360000, -40360994252587008000, 86532649452872663040]

theorem f415_relative_gram_check :
    b415relativeᵀ*natFourWordGram f415basis*b415relative=f415relativeGram := by
  have hG : natFourWordGram f415basis=Matrix.diagonal (fun a => (f415wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f415_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 360360 f415GramIntegerCoordinates=b415relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 54, f415GramIntegerCoordinates a i*(f415wordMetric a : ℤ)*
      f415GramIntegerCoordinates a j)=f415GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 54, f415GramIntegerCoordinates a 0*
          (f415wordMetric a : ℤ)*f415GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f415GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 54, f415GramIntegerCoordinates a 1*
          (f415wordMetric a : ℤ)*f415GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f415GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 54, f415GramIntegerCoordinates a 2*
          (f415wordMetric a : ℤ)*f415GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f415GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 54, f415GramIntegerCoordinates a 3*
          (f415wordMetric a : ℤ)*f415GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f415GramIntegerForm 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 54, f415GramIntegerCoordinates a 4*
          (f415wordMetric a : ℤ)*f415GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f415GramIntegerForm 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 54, f415GramIntegerCoordinates a 5*
          (f415wordMetric a : ℤ)*f415GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f415GramIntegerForm 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 7) => ∑ a : Fin 54, f415GramIntegerCoordinates a 6*
          (f415wordMetric a : ℤ)*f415GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 7) => f415GramIntegerForm 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (360360*360360) f415GramIntegerForm=f415relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 360360 f415wordMetric
    f415GramIntegerCoordinates f415GramIntegerForm b415relative f415relativeGram hU hY hF

theorem f415_actual_relative_gram :
    natFamilyGram f415relativeFamily=complexify f415relativeGram := by
  rw [f415relativeFamily,natFourColumnFamily_gram f415basis f415_occupation_injective,
    f415_relative_gram_check]

theorem f415_relative_gram_inverse_right :
    f415relativeGram*f415relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f415_relative_gram_inverse_left :
    f415relativeGramInverse*f415relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f415_relative_gram_inverse_symmetric :
    f415relativeGramInverseᵀ=f415relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f415_word_metric_check
#print axioms f415_relative_gram_check
#print axioms f415_actual_relative_gram
#print axioms f415_relative_gram_inverse_right
#print axioms f415_relative_gram_inverse_left
#print axioms f415_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
