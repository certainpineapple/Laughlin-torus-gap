/- Reconstruct the anchored planar N=3 matrix from all original integer rows.
No finite torus h projection is assumed. -/
import torus.shared.BosonFiniteCertificatePlanar
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
namespace TorusLean.BosonFiniteCertificate

def p302basis : Fin 2 → List ℕ := ![[0, 0, 2], [0, 1, 1]]

theorem p302_basis_enumerated :
    (List.finRange 2).map p302basis = threeBasis 2 := by decide +kernel

def p302action0 : Matrix (Fin 31) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    -183423658, -32000;
    -270835556, -177292;
    -87804058, -90618;
    -111904224, 1366184;
    -212870796, 495858;
    -299609218, -1390844;
    -112464518, 714710;
    -336852720, 5250918;
    -103474828, -7493704;
    -406805644, 764558;
    1235459020, 8926904;
    -1077867092, -59820120;
    -10093997614, 867143646;
    28848043672, -3374898504;
    1512907668, -6570738806;
    70667046586, -29975676732;
    35178452722, -9608132832;
    12387764490, 29665380668;
    -122868588574, -8351529836;
    178580477478, -174224588708;
    -200487319182, -35306937418;
    80345524216, 74728371266;
    -194926785444, -260802087472;
    -607631856906, -302317809380;
    -1112387884736, -14744015576]

def p302action0Raw : Matrix (Fin 31) (Fin 2) ℤ := fun r i => threeRowAction 0 ((frozenRows 0)[r.val]?.getD []) (p302basis i)

theorem p302action0_reconstructed : p302action0Raw = p302action0 := by decide +kernel

def p302pair0 : Matrix (Fin 31) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    -184440892, 0;
    -270781370, 0;
    -87783962, 0;
    -109233680, 0;
    -210924126, 0;
    -305550218, 0;
    -111569764, 0;
    -322948290, 0;
    -120075154, 0;
    -404987894, 0;
    1259200420, 0;
    411852294, 0;
    -7250503376, 0;
    20274697840, 0;
    -17125238914, 0;
    2316543276, 0;
    -1025142790, 0;
    105157191858, 0;
    -150256084544, 0;
    39925542332, 0;
    -3572834096, 0;
    5396784272, 0;
    130240177474, 0;
    -305866267180, 0;
    -790761512574, 0]

def p302pair0Raw : Matrix (Fin 31) (Fin 2) ℤ := fun r i => rowInteger ((frozenRows 0)[r.val]?.getD []) 0 * (pairRemoval (p302basis i) 0 : ℤ)

theorem p302pair0_reconstructed : p302pair0Raw = p302pair0 := by decide +kernel

def p302action1 : Matrix (Fin 37) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    -28310, -69977386;
    -100848, -242205580;
    -1715302, -605630092;
    1840210, -94222696;
    -465616, -643032024;
    -2780472, -278744864;
    3252712, -308907494;
    2752898, -817704898;
    11655692, -114201958;
    5927586, -426540174;
    -3297020, 1836101774;
    -377571392, 719479620;
    219121736, -5255460946;
    -648157392, 5961429342;
    2562548644, -11999059632;
    5632376684, 64168478328;
    21367016590, -77673823106;
    -137889480212, 109703112118;
    -138927222176, 22878379384;
    89494233012, 84641776378;
    -13749291990, -121493822720;
    -101529083388, 192247040806;
    -106116409552, 61698933880;
    -259744750428, -422379235144;
    -141053722268, 76556838450;
    -336669390204, -335448828584;
    -88088022896, -282701506408;
    877688884900, 190361871006]

def p302action1Raw : Matrix (Fin 37) (Fin 2) ℤ := fun r i => threeRowAction 1 ((frozenRows 1)[r.val]?.getD []) (p302basis i)

theorem p302action1_reconstructed : p302action1Raw = p302action1 := by decide +kernel

def p302pair1 : Matrix (Fin 37) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, -69931640;
    0, -242488596;
    0, -606731888;
    0, -92917128;
    0, -642109256;
    0, -277988776;
    0, -306664492;
    0, -818060716;
    0, -108239244;
    0, -425919464;
    0, 1848199056;
    0, 455529944;
    0, -5233054824;
    0, 5633650440;
    0, -10651465640;
    0, 76824848200;
    0, -78783015408;
    0, 48114198320;
    0, -71596185240;
    0, 86159473288;
    0, -132144103868;
    0, 74736798764;
    0, 141477828348;
    0, -120391457056;
    0, 73950695916;
    0, -57747617192;
    0, -50186440304;
    0, -203983191856]

def p302pair1Raw : Matrix (Fin 37) (Fin 2) ℤ := fun r i => rowInteger ((frozenRows 1)[r.val]?.getD []) 0 * (pairRemoval (p302basis i) 1 : ℤ)

theorem p302pair1_reconstructed : p302pair1Raw = p302pair1 := by decide +kernel

def p302action2 : Matrix (Fin 36) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    -72624910, -36371508;
    -125978952, -63008766;
    -49572938, -26119274;
    -571964398, -286438620;
    -95034114, -48004424;
    -682918334, -340838570;
    -662099148, -330735252;
    1078737656, 539707460;
    -81016592, -40310178;
    38854168, 24492342;
    181870024, 93708058;
    1722631124, 850545382;
    380042810, 194752202;
    2804498126, 1401610482;
    -2018919254, -1001017396;
    9285235416, 4735923892;
    -6909246068, -4319030594;
    48351957150, 16882581594;
    -159324973392, -21903791816;
    -9799622286, -1533951834;
    55230832190, -25631450240;
    111399635104, -49606643712;
    177932272720, -117335100068;
    -70696460804, -41052252166;
    -13263913848, 5161334706;
    -22251679556, -2156850344;
    205531679578, 198313642698;
    13137293508, -6511485862;
    696011666682, 736120299264;
    -248252189688, -463165324590]

def p302action2Raw : Matrix (Fin 36) (Fin 2) ℤ := fun r i => threeRowAction 2 ((frozenRows 2)[r.val]?.getD []) (p302basis i)

theorem p302action2_reconstructed : p302action2Raw = p302action2 := by decide +kernel

def p302pair2 : Matrix (Fin 36) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    -72714352, -36357176;
    -125967536, -62983768;
    -51034084, -25517042;
    -572635992, -286317996;
    -95709796, -47854898;
    -682698116, -341349058;
    -661443636, -330721818;
    1079844216, 539922108;
    -82916740, -41458370;
    43912364, 21956182;
    186745604, 93372802;
    1712587404, 856293702;
    388292556, 194146278;
    2804817232, 1402408616;
    -2007583892, -1003791946;
    9360882892, 4680441446;
    -9835651020, -4917825510;
    44860884784, 22430442392;
    -110463934748, -55231967374;
    10100809240, 5050404620;
    -8505558940, -4252779470;
    4956664148, 2478332074;
    -34367943492, -17183971746;
    4317922588, 2158961294;
    25153576968, 12576788484;
    110333503572, 55166751786;
    -83921579404, -41960789702;
    -83580158260, -41790079130;
    225757386264, 112878693132;
    -474014021556, -237007010778]

def p302pair2Raw : Matrix (Fin 36) (Fin 2) ℤ := fun r i => rowInteger ((frozenRows 2)[r.val]?.getD []) 0 * (pairRemoval (p302basis i) 2 : ℤ)

theorem p302pair2_reconstructed : p302pair2Raw = p302pair2 := by decide +kernel

def p302action3 : Matrix (Fin 34) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0]

def p302action3Raw : Matrix (Fin 34) (Fin 2) ℤ := fun r i => threeRowAction 3 ((frozenRows 3)[r.val]?.getD []) (p302basis i)

theorem p302action3_reconstructed : p302action3Raw = p302action3 := by decide +kernel

def p302pair3 : Matrix (Fin 34) (Fin 2) ℤ :=
  !![0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0;
    0, 0]

def p302pair3Raw : Matrix (Fin 34) (Fin 2) ℤ := fun r i => rowInteger ((frozenRows 3)[r.val]?.getD []) 0 * (pairRemoval (p302basis i) 3 : ℤ)

theorem p302pair3_reconstructed : p302pair3Raw = p302pair3 := by decide +kernel

def p302rawNumerator : Matrix (Fin 2) (Fin 2) ℤ :=
  (2 : ℤ) • ((p302action0Raw)ᵀ * p302action0Raw - (p302pair0Raw)ᵀ * p302pair0Raw) +
    (1 : ℤ) • ((p302action1Raw)ᵀ * p302action1Raw - (p302pair1Raw)ᵀ * p302pair1Raw) +
    (1 : ℤ) • ((p302action2Raw)ᵀ * p302action2Raw - (p302pair2Raw)ᵀ * p302pair2Raw)

def p302numerator : Matrix (Fin 2) (Fin 2) ℤ :=
  !![3345765541313051699024968, 1319140405642074190073628;
    1319140405642074190073628, 1494149521235811978131904]

theorem p302_numerator_reconstructed :
    p302rawNumerator = p302numerator := by
  unfold p302rawNumerator
  simp only [p302action0_reconstructed, p302pair0_reconstructed, p302action1_reconstructed, p302pair1_reconstructed, p302action2_reconstructed, p302pair2_reconstructed, p302action3_reconstructed, p302pair3_reconstructed]
  decide +kernel

def p302Mform : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(418220692664131462378121/125000000000000000000000), (329785101410518547518407/250000000000000000000000);
    (329785101410518547518407/250000000000000000000000), (23346086269309562158311/15625000000000000000000)]

def p302rawMform : Matrix (Fin 2) (Fin 2) ℚ :=
  integerForm p302rawNumerator

theorem p302_Mform_reconstructed : p302rawMform = p302Mform := by
  unfold p302rawMform
  rw [p302_numerator_reconstructed]
  decide +kernel

def p302Hform : Matrix (Fin 2) (Fin 2) ℚ :=
  !![8, 2;
    2, 5]

def p302Sform : Matrix (Fin 2) (Fin 2) ℚ :=
  !![10, 7;
    7, (17/2)]

def p302Ginv : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.diagonal ![(1/4), (1/2)]

def p302rawHform : Matrix (Fin 2) (Fin 2) ℚ := fun i j => planarHForm 2 (p302basis i) (p302basis j)

theorem p302_Hform_reconstructed :
    p302rawHform = p302Hform := by decide +kernel

theorem p302_Sform_reconstructed :
    planarSingleForm p302Ginv p302Hform = p302Sform := by decide +kernel

#print axioms p302action0_reconstructed
#print axioms p302pair0_reconstructed
#print axioms p302action1_reconstructed
#print axioms p302pair1_reconstructed
#print axioms p302action2_reconstructed
#print axioms p302pair2_reconstructed
#print axioms p302action3_reconstructed
#print axioms p302pair3_reconstructed
#print axioms p302_basis_enumerated
#print axioms p302_numerator_reconstructed
#print axioms p302_Mform_reconstructed
#print axioms p302_Hform_reconstructed
#print axioms p302_Sform_reconstructed

end TorusLean.BosonFiniteCertificate
