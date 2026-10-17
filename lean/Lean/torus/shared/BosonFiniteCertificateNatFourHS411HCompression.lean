import torus.shared.BosonFiniteCertificateNatFourHS411HSource

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private def f411HCompressionInteger : Matrix (Fin 27) (Fin 27) ℤ :=
  !![1438408125, 467775, 467775, 467775, 467775, 467775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    467775, 43758225, 155925, 155925, 155925, 155925, 56700, 28350, 28350, 28350, 28350, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    467775, 155925, 5984685, 155925, 155925, 155925, 1451520, 11340, 0, 0, 0, 22680, 11340, 11340, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    467775, 155925, 155925, 1622565, 155925, 155925, 0, 241920, 7560, 0, 0, 0, 7560, 0, 15120, 7560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    467775, 155925, 155925, 155925, 775845, 155925, 0, 0, 60480, 7560, 0, 60480, 0, 7560, 0, 15120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    467775, 155925, 155925, 155925, 155925, 566325, 0, 0, 0, 21600, 21600, 0, 21600, 10800, 10800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 56700, 1451520, 0, 0, 0, 3691170, 28350, 28350, 28350, 28350, 0, 0, 0, 0, 0, 17010, 5670, 5670, 5670, 0, 0, 0, 0, 0, 0, 0;
    0, 28350, 11340, 241920, 0, 0, 28350, 383985, 14175, 14175, 14175, 11340, 5670, 5670, 0, 0, 241920, 2520, 0, 0, 2520, 1260, 1260, 0, 0, 0, 0;
    0, 28350, 0, 7560, 60480, 0, 28350, 14175, 124740, 14175, 14175, 30240, 3780, 0, 7560, 3780, 0, 30240, 1890, 0, 0, 945, 0, 1890, 0, 0, 0;
    0, 28350, 0, 0, 7560, 21600, 28350, 14175, 14175, 68715, 14175, 0, 10800, 3780, 0, 7560, 0, 0, 8640, 2160, 4320, 0, 2160, 1080, 0, 0, 0;
    0, 28350, 0, 0, 0, 21600, 28350, 14175, 14175, 14175, 100575, 0, 0, 10800, 10800, 0, 0, 0, 0, 7200, 0, 3600, 0, 0, 0, 0, 0;
    0, 0, 22680, 0, 60480, 0, 0, 11340, 30240, 0, 0, 134820, 11340, 11340, 0, 0, 0, 40320, 0, 0, 1260, 0, 0, 0, 3780, 1260, 0;
    0, 0, 11340, 7560, 0, 21600, 0, 5670, 3780, 10800, 0, 11340, 33750, 5670, 7560, 3780, 0, 0, 8640, 0, 8640, 540, 0, 0, 0, 1080, 1620;
    0, 0, 11340, 0, 7560, 10800, 0, 5670, 0, 3780, 10800, 11340, 5670, 22770, 5400, 7560, 0, 0, 0, 5760, 0, 1440, 1440, 0, 4320, 1440, 0;
    0, 0, 0, 15120, 0, 10800, 0, 0, 7560, 0, 10800, 0, 7560, 5400, 30240, 7560, 0, 0, 0, 0, 0, 4320, 0, 1080, 0, 0, 3240;
    0, 0, 0, 7560, 15120, 0, 0, 0, 3780, 7560, 0, 0, 3780, 7560, 7560, 25812, 0, 0, 0, 0, 0, 0, 3456, 3456, 0, 1728, 0;
    0, 0, 0, 0, 0, 0, 17010, 241920, 0, 0, 0, 0, 0, 0, 0, 0, 776790, 17010, 17010, 17010, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 5670, 2520, 30240, 0, 0, 40320, 0, 0, 0, 0, 17010, 91350, 5670, 5670, 5040, 2520, 2520, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 5670, 0, 1890, 8640, 0, 0, 8640, 0, 0, 0, 17010, 5670, 35370, 5670, 8640, 1890, 0, 3780, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 5670, 0, 0, 2160, 7200, 0, 0, 5760, 0, 0, 17010, 5670, 5670, 22950, 0, 3600, 4320, 2160, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 2520, 0, 4320, 0, 1260, 8640, 0, 0, 0, 0, 5040, 8640, 0, 27900, 2520, 2520, 0, 3780, 1260, 0;
    0, 0, 0, 0, 0, 0, 0, 1260, 945, 0, 3600, 0, 540, 1440, 4320, 0, 0, 2520, 1890, 3600, 2520, 8145, 1260, 1890, 4320, 1080, 1620;
    0, 0, 0, 0, 0, 0, 0, 1260, 0, 2160, 0, 0, 0, 1440, 0, 3456, 0, 2520, 0, 4320, 2520, 1260, 11916, 2160, 0, 2880, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1890, 1080, 0, 0, 0, 0, 1080, 3456, 0, 0, 3780, 2160, 0, 1890, 2160, 9396, 0, 1728, 3240;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3780, 0, 4320, 0, 0, 0, 0, 0, 0, 3780, 4320, 0, 0, 24300, 3780, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1260, 1080, 1440, 0, 1728, 0, 0, 0, 0, 1260, 1080, 2880, 1728, 3780, 7164, 3240;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1620, 0, 3240, 0, 0, 0, 0, 0, 0, 1620, 0, 3240, 0, 3240, 14580]

private def f411HCompressionCoordinates : Matrix (Fin 27) (Fin 4) ℤ :=
  !![10, (-12), (-12), 21;
    (-110), 132, 132, (-231);
    350, (-276), (-204), 285;
    (-750), 252, 180, (-117);
    900, (-72), (-72), 0;
    (-420), 0, 0, 0;
    200, (-384), (-456), 870;
    (-900), 1728, 1296, (-2214);
    2400, (-1728), (-1152), 936;
    (-4200), 504, 504, 0;
    2520, 0, 0, 0;
    0, (-2160), (-720), 1458;
    0, 5040, 1008, (-1260);
    0, (-1512), (-504), 0;
    0, (-4032), 0, 252;
    0, 2520, 0, 0;
    0, 0, 504, (-1134);
    0, 0, (-2016), 4536;
    0, 0, 2016, (-2016);
    0, 0, (-1008), 0;
    0, 0, 2016, (-6426);
    0, 0, (-4032), 6048;
    0, 0, 2520, 0;
    0, 0, 0, (-1260);
    0, 0, 0, 3402;
    0, 0, 0, (-5670);
    0, 0, 0, 2520]

private def f411HCompressionLeftProduct : Matrix (Fin 4) (Fin 27) ℤ :=
  !![14370048000, (-4790016000), 2320164000, (-1299564000), 671328000, (-208656000), 1234926000, (-510300000), 314118000, (-231336000), 208656000, 124740000, (-52164000), 12474000, 29484000, (-14742000), (-214326000), 71442000, (-30618000), 10206000, (-20412000), 10206000, (-10206000), 0, 0, 0, 0;
    (-17244057600), 5748019200, (-2155507200), 770757120, (-249298560), 59875200, (-1796256000), 692375040, (-260729280), 94711680, (-59875200), (-294477120), 123560640, (-25038720), (-82192320), 40279680, 411505920, (-137168640), 42456960, (-9797760), 47355840, (-16329600), 9797760, 1632960, (-14696640), 4898880, (-4898880);
    (-17244057600), 5748019200, (-1846877760), 576434880, (-157852800), 27216000, (-1950570720), 635221440, (-209291040), 65318400, (-27216000), (-199221120), 63141120, (-15513120), (-18506880), 8436960, 680127840, (-226709280), 80831520, (-22589280), 72938880, (-29121120), 22589280, 1632960, (-14696640), 4898880, (-4898880);
    30177100800, (-10059033600), 2917691280, (-705846960), 144789120, (-24494400), 3570671160, (-1105922160), 280528920, (-60147360), 24494400, 372450960, (-102468240), 16669800, 36333360, (-14356440), (-1358826840), 452942280, (-117913320), 18983160, (-167514480), 49465080, (-18983160), (-7620480), 68584320, (-22861440), 22861440]

private def f411HCompressionResult : Matrix (Fin 4) (Fin 4) ℤ :=
  !![6106726080000, (-4543547904000), (-3843987840000), 5796518112000;
    (-4543547904000), 5886807736320, 4741175255040, (-8009551226880);
    (-3843987840000), 4741175255040, 4966131824640, (-8657261544960);
    5796518112000, (-8009551226880), (-8657261544960), 16009294896000]

theorem f411_relative_H_compression :
    b411relativeᵀ*f411rawHForm*b411relative=b411h := by
  have hM : natFourIntegerMatrix 2 f411HCompressionInteger=f411rawHForm := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f411HCompressionInteger) (f411rawHForm) (by decide +kernel) a b
  have hD : natFourIntegerMatrix 2520 f411HCompressionCoordinates=b411relative := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2520 f411HCompressionCoordinates) (b411relative) (by decide +kernel) a b
  have hV : f411HCompressionCoordinatesᵀ*f411HCompressionInteger=f411HCompressionLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionCoordinatesᵀ*f411HCompressionInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionCoordinatesᵀ*f411HCompressionInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionCoordinatesᵀ*f411HCompressionInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionCoordinatesᵀ*f411HCompressionInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411HCompressionLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f411HCompressionLeftProduct*f411HCompressionCoordinates=f411HCompressionResult := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionLeftProduct*f411HCompressionCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionResult) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionLeftProduct*f411HCompressionCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionResult) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionLeftProduct*f411HCompressionCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionResult) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionLeftProduct*f411HCompressionCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f411HCompressionResult) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2520*2*2520) f411HCompressionResult=b411h := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2520*2*2520) f411HCompressionResult) (b411h) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 2 2520
    f411HCompressionInteger f411HCompressionCoordinates f411HCompressionLeftProduct f411HCompressionResult
    f411rawHForm b411relative b411h hM hD hV hY hF

theorem f411_actual_relative_H_form (x y : Fin 4 → ℂ) :
    natOccupationInner (natFourWordBlock f411basis (complexify b411relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f411basis (complexify b411relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b411h *ᵥ y) :=
  natFour_operator_relative_matrix_form f411basis b411relative canonicalPairHamiltonianNat
    f411rawHForm b411h f411_actual_raw_H_matrix
    f411_relative_H_compression x y

#print axioms f411_relative_H_compression
#print axioms f411_actual_relative_H_form
end TorusLean.BosonFiniteCertificate
