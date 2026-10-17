import torus.shared.BosonFiniteCertificateNatFourRelativeGramIntegerCore
import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourBasis414
import torus.shared.BosonFiniteCertificate414

/-! Degree-14 actual relative-family factorial Gram and its two-sided inverse.
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

def f414wordMetric : Fin 47 → ℕ := ![523069747200, 12454041600, 1916006400, 479001600, 174182400, 87091200, 58060800, 101606400, 958003200, 79833600, 21772800, 8709120, 4838400, 3628800, 29030400, 4354560, 1935360, 1209600, 2073600, 2903040, 725760, 518400, 829440, 691200, 239500800, 14515200, 4354560, 1935360, 1209600, 2073600, 2903040, 483840, 241920, 172800, 362880, 103680, 172800, 138240, 1935360, 241920, 138240, 230400, 103680, 34560, 165888, 155520, 82944]

def f414relativeGram : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(69380236800/143), (-5034355200/143), (1869235200/143), (-454809600/13), (1486598400/143), (1397491200/143), (-139668480/13), (-1238630400/143);
    (-5034355200/143), (27234316800/1001), (-20201241600/1001), (1584230400/91), (-13651488000/1001), (-1694016000/143), (1609067520/91), (15391641600/1001);
    (1869235200/143), (-20201241600/1001), (39454924800/1001), (-1147852800/91), (19547328000/1001), (14789452800/1001), (-359147520/13), (-24264990720/1001);
    (-454809600/13), (1584230400/91), (-1147852800/91), (26430105600/1001), (-13279334400/1001), (-13387161600/1001), (18544988160/1001), (2395975680/143);
    (1486598400/143), (-13651488000/1001), (19547328000/1001), (-13279334400/1001), (18813878400/1001), (2475091200/143), (-4458309120/143), (-2734479360/91);
    (1397491200/143), (-1694016000/143), (14789452800/1001), (-13387161600/1001), (2475091200/143), (2713792000/143), (-32390568960/1001), (-32579665920/1001);
    (-139668480/13), (1609067520/91), (-359147520/13), (18544988160/1001), (-4458309120/143), (-32390568960/1001), (306101864448/5005), (44808855552/715);
    (-1238630400/143), (15391641600/1001), (-24264990720/1001), (2395975680/143), (-2734479360/91), (-32579665920/1001), (44808855552/715), (67061108736/1001)]

def f414relativeGramInverse : Matrix (Fin 8) (Fin 8) ℚ :=
  !![(4113713/1704672519782400), (1341/429496729600), (6353/11596411699200), (36587/11596411699200), (8957/2899102924800), (4619/1288490188800), (2239/927712935936), (-175/1391569403904);
    (1341/429496729600), (3350569/34789235097600), (116383/3865470566400), (-202903/6957847019520), (6401/115964116992), (181997/3865470566400), (22225/309237645312), (-10721/463856467968);
    (6353/11596411699200), (116383/3865470566400), (867043/11596411699200), (-158063/11596411699200), (-316249/2899102924800), (249299/3865470566400), (36557/927712935936), (-14303/463856467968);
    (36587/11596411699200), (-202903/6957847019520), (-158063/11596411699200), (702157/6957847019520), (236861/2899102924800), (151243/1288490188800), (27349/309237645312), (-16879/1391569403904);
    (8957/2899102924800), (6401/115964116992), (-316249/2899102924800), (236861/2899102924800), (149279/144955146240), (-80297/966367641600), (187849/231928233984), (-47347/115964116992);
    (4619/1288490188800), (181997/3865470566400), (249299/3865470566400), (151243/1288490188800), (-80297/966367641600), (1135171/1288490188800), (154717/309237645312), (-14479/154618822656);
    (2239/927712935936), (22225/309237645312), (36557/927712935936), (27349/309237645312), (187849/231928233984), (154717/309237645312), (3040075/1855425871872), (-881705/927712935936);
    (-175/1391569403904), (-10721/463856467968), (-14303/463856467968), (-16879/1391569403904), (-47347/115964116992), (-14479/154618822656), (-881705/927712935936), (103985/154618822656)]

def f414relativeFamily : Fin 8 → Core ℕ ℂ :=
  natFourColumnFamily f414basis b414relative

theorem f414_word_metric_check : ∀ a,
    natFourWordMetric (f414basis a)=f414wordMetric a := by
  have h : ∀ a, natFourComputableMetric (f414basis a)=f414wordMetric a := by
    decide +kernel
  simpa only [natFourComputableMetric_eq] using h

private def f414GramIntegerCoordinates : Matrix (Fin 47) (Fin 8) ℤ :=
  !![-105, 105, -140, 105, -140, -140, 252, 252;
    1470, -1470, 1960, -1470, 1960, 1960, -3528, -3528;
    -9555, 5265, -5590, 4875, -4420, -4030, 6552, 6006;
    38220, -12480, 8060, -12480, 5915, 5200, -5928, -4212;
    -105105, 19305, -5720, 19305, -4290, -4290, 2288, 858;
    210210, -17160, 1430, -17160, 1430, 1430, 0, 0;
    -315315, 6435, 0, 6435, 0, 0, 0, 0;
    180180, 0, 0, 0, 0, 0, 0, 0;
    0, 4290, -7150, 4680, -8320, -8710, 16380, 16926;
    0, -25740, 42900, -21060, 35295, 32760, -60840, -59436;
    0, 60060, -65780, 60060, -47905, -40040, 56056, 42900;
    0, -107250, 50050, -107250, 35750, 35750, -22880, -8580;
    0, 115830, -12870, 115830, -12870, -12870, 0, 0;
    0, -51480, 0, -51480, 0, 0, 0, 0;
    0, 25740, -68640, 0, -34320, -24310, 56628, 54054;
    0, -85800, 228800, 0, 89375, 42900, -106392, -80652;
    0, 193050, -193050, 0, -64350, -42900, 46332, 15444;
    0, -308880, 51480, 0, 25740, 17160, 0, 0;
    0, 180180, 0, 0, 0, 0, 0, 0;
    0, 0, -214500, 0, -53625, 0, 51480, 30888;
    0, 0, 429000, 0, 64350, 0, -48048, -10296;
    0, 0, -120120, 0, -30030, 0, 0, 0;
    0, 0, -300300, 0, 0, 0, 12012, 0;
    0, 0, 180180, 0, 0, 0, 0, 0;
    0, 0, 0, -4680, 9750, 13000, -24960, -28080;
    0, 0, 0, 25740, -53625, -71500, 137280, 154440;
    0, 0, 0, -85800, 78650, 85800, -128128, -116688;
    0, 0, 0, 193050, -64350, -85800, 56628, 23166;
    0, 0, 0, -308880, 25740, 34320, 0, 0;
    0, 0, 0, 180180, 0, 0, 0, 0;
    0, 0, 0, 0, 75075, 114400, -247104, -298584;
    0, 0, 0, 0, -225225, -214500, 463320, 478764;
    0, 0, 0, 0, 193050, 257400, -226512, -92664;
    0, 0, 0, 0, -90090, -120120, 0, 0;
    0, 0, 0, 0, 171600, 0, -219648, -205920;
    0, 0, 0, 0, -300300, 0, 240240, 72072;
    0, 0, 0, 0, 180180, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -72072, 0;
    0, 0, 0, 0, 0, -64350, 138996, 208494;
    0, 0, 0, 0, 0, 171600, -370656, -555984;
    0, 0, 0, 0, 0, -300300, 216216, 108108;
    0, 0, 0, 0, 0, 180180, 0, 0;
    0, 0, 0, 0, 0, 0, 288288, 576576;
    0, 0, 0, 0, 0, 0, -432432, -216216;
    0, 0, 0, 0, 0, 0, 180180, 0;
    0, 0, 0, 0, 0, 0, 0, -288288;
    0, 0, 0, 0, 0, 0, 0, 180180]

private def f414GramIntegerForm : Matrix (Fin 8) (Fin 8) ℤ :=
  !![15751173143946240000, -1142933551119360000, 424366485903360000, -1135793649070080000, 337497677637120000, 317267955164160000, -348793368827904000, -281202296094720000;
    -1142933551119360000, 883274256184320000, -655174748067840000, 565184334274560000, -442750519411200000, -384587031628800000, 574045135792128000, 499187877027840000;
    424366485903360000, -655174748067840000, 1279617903083520000, -409503832657920000, 633966760627200000, 479657448990720000, -896897234128896000, -786971885027328000;
    -1135793649070080000, 565184334274560000, -409503832657920000, 857191756861440000, -430680684994560000, -434177779875840000, 601458474000384000, 543950691508224000;
    337497677637120000, -442750519411200000, 633966760627200000, -430680684994560000, 610179229820160000, 561912034844160000, -1012155652924416000, -975543012347904000;
    317267955164160000, -384587031628800000, 479657448990720000, -434177779875840000, 561912034844160000, 616103513625600000, -1050503888738304000, -1056636756983808000;
    -348793368827904000, 574045135792128000, -896897234128896000, 601458474000384000, -1012155652924416000, -1050503888738304000, 1985523621704663040, 2034562217526558720;
    -281202296094720000, 499187877027840000, -786971885027328000, 543950691508224000, -975543012347904000, -1056636756983808000, 2034562217526558720, 2174952702969446400]

theorem f414_relative_gram_check :
    b414relativeᵀ*natFourWordGram f414basis*b414relative=f414relativeGram := by
  have hG : natFourWordGram f414basis=Matrix.diagonal (fun a => (f414wordMetric a : ℚ)) := by
    unfold natFourWordGram
    congr 1
    funext a
    rw [f414_word_metric_check]
  rw [hG]
  have hU : natFourIntegerMatrix 180180 f414GramIntegerCoordinates=b414relative := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  have hY : ∀ i j, (∑ a : Fin 47, f414GramIntegerCoordinates a i*(f414wordMetric a : ℤ)*
      f414GramIntegerCoordinates a j)=f414GramIntegerForm i j := by
    intro i j
    fin_cases i
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 0*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 1*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 2*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 3*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 4*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 5*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 6*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 8) => ∑ a : Fin 47, f414GramIntegerCoordinates a 7*
          (f414wordMetric a : ℤ)*f414GramIntegerCoordinates a j)
        (fun (_ : Fin 1) (j : Fin 8) => f414GramIntegerForm 7 j) (by decide +kernel)
      exact congrFun (congrFun h 0) j
  have hF : natFourIntegerMatrix (180180*180180) f414GramIntegerForm=f414relativeGram := by
    ext i j
    exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j
  exact natFour_integer_weighted_compression_check 180180 f414wordMetric
    f414GramIntegerCoordinates f414GramIntegerForm b414relative f414relativeGram hU hY hF

theorem f414_actual_relative_gram :
    natFamilyGram f414relativeFamily=complexify f414relativeGram := by
  rw [f414relativeFamily,natFourColumnFamily_gram f414basis f414_occupation_injective,
    f414_relative_gram_check]

theorem f414_relative_gram_inverse_right :
    f414relativeGram*f414relativeGramInverse=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f414_relative_gram_inverse_left :
    f414relativeGramInverse*f414relativeGram=1 := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

theorem f414_relative_gram_inverse_symmetric :
    f414relativeGramInverseᵀ=f414relativeGramInverse := by
  ext i j
  exact natFourRationalEntryCheck_sound _ _ (by decide +kernel) i j

#print axioms f414_word_metric_check
#print axioms f414_relative_gram_check
#print axioms f414_actual_relative_gram
#print axioms f414_relative_gram_inverse_right
#print axioms f414_relative_gram_inverse_left
#print axioms f414_relative_gram_inverse_symmetric
end TorusLean.BosonFiniteCertificate
