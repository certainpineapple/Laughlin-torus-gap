import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate407

/-! Genuine Nat COM descendants of the original relative basis, with every
step checked against independently verified raising actions and every form
checked against independently reconstructed raw source M4 matrices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f407desc7Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(167047079157387264918849462423/7812500000000000000000), (19923219707428323581832711657/976562500000000000000);
    (19923219707428323581832711657/976562500000000000000), (13103444368739063262933533727/488281250000000000000)]

private def f407desc7IntegerCoordinates : Matrix (Fin 47) (Fin 2) ℤ :=
  !![3, (-4);
    42, (-56);
    69, (-72);
    48, 56;
    27, 224;
    6, 152;
    (-105), (-140);
    (-96), (-152);
    120, (-180);
    36, (-88);
    (-300), 840;
    120, 920;
    324, (-192);
    (-504), (-1008);
    (-504), 372;
    (-1260), 520;
    (-90), (-1040);
    (-1080), 80;
    (-1344), 952;
    (-360), (-1400);
    (-240), (-2240);
    (-2184), 4592;
    210, 1960;
    504, 4648;
    0, (-80);
    (-756), 608;
    0, 720;
    2520, (-940);
    2304, (-992);
    420, 0;
    (-1260), 880;
    3780, (-4440);
    6840, (-5520);
    (-2016), 6048;
    3840, (-6720);
    4200, (-11760);
    0, (-3360);
    6300, (-14560);
    0, 60;
    0, 2080;
    (-7560), 11480;
    (-6804), 9072;
    (-8400), 11200;
    (-12600), 10640;
    3150, (-5600);
    0, 2240;
    12600, (-9800)]

private def f407desc7IntegerLeftProduct : Matrix (Fin 2) (Fin 47) ℤ :=
  !![0, 0, 0, 0, 0, 0, (-116950021213791929625249584025600), (-216131469646920897311045062963200), 0, 0, 0, 0, (-263914804590223021152299827200), (-51348570459977363762808526924800), 0, 0, 231341725061143895035850342400, (-1981325843320044413059812403200), (-17595354386544075927010542643200), 11470501776861804911263948800, (-465503560306724932831767398400), (-1829332542630262717137371904000), 1679883225453572931465703142400, 0, 0, 0, 0, 34057894866112859776996147200, (-641424052293090600080189260800), (-18789644425245084411707906150400), 0, (-18430982476170806380795084800), (-970073761212643025676305433600), (-1301943984137327470648583347200), 1670778773057520393104886451200, 283504179124604476766935065600, 0, 0, 148951363465827617586000076800, (-173693218875351512719274726400), 1408037756968043965604405376000, 0, (-515729847853859735583151257600), 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (-105584452911721058541650954035200), (-294202695758639079075153393254400), 0, 0, 0, 0, (-881028126973300844818744934400), (-48728871367794305701598933913600), 0, 0, 772289328701271812799990988800, (-1723454025129079570639110758400), (-15059222077751669637287658086400), 38292061103797431419906457600, 330882415464836781326566195200, 1157791159899707320066028544000, (-1167545790744461713527060787200), 0, 0, 0, 0, 113695741993826788086974054400, (-1468463631843290909815960473600), (-13705997688067098328059311308800), 0, (-61528193757498422737959321600), (-730737810288964750636778803200), 1249610042573827378846701465600, 1790945066700904441496904806400, (-5246532371094831807421132800), 0, 0, 497245138088650747817191833600, 474334447661314248710409523200, (-590039844539260427640921600000), 0, 480440531159986395298045132800, 0, 0, 0, 0]

private def f407desc7IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![76975294075724051674605832284518400, 73444957129463772052068108252364800;
    73444957129463772052068108252364800, 96609074641839365624956357462425600]

private theorem f407desc7_coordinates_decode : natFourIntegerMatrix 60 f407desc7IntegerCoordinates=f407desc7 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc7IntegerCoordinates) (f407desc7) (by decide +kernel) a b

#print axioms f407desc7_coordinates_decode

private theorem f407desc7_left_row0_columns0 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 0=f407desc7IntegerLeftProduct 0 0) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 1=f407desc7IntegerLeftProduct 0 1) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 2=f407desc7IntegerLeftProduct 0 2) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 3=f407desc7IntegerLeftProduct 0 3) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 4=f407desc7IntegerLeftProduct 0 4) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 5=f407desc7IntegerLeftProduct 0 5) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 6=f407desc7IntegerLeftProduct 0 6) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 7=f407desc7IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f407desc7_left_row0_columns0

private theorem f407desc7_left_row0_columns1 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 8=f407desc7IntegerLeftProduct 0 8) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 9=f407desc7IntegerLeftProduct 0 9) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 10=f407desc7IntegerLeftProduct 0 10) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 11=f407desc7IntegerLeftProduct 0 11) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 12=f407desc7IntegerLeftProduct 0 12) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 13=f407desc7IntegerLeftProduct 0 13) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 14=f407desc7IntegerLeftProduct 0 14) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 15=f407desc7IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f407desc7_left_row0_columns1

private theorem f407desc7_left_row0_columns2 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 16=f407desc7IntegerLeftProduct 0 16) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 17=f407desc7IntegerLeftProduct 0 17) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 18=f407desc7IntegerLeftProduct 0 18) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 19=f407desc7IntegerLeftProduct 0 19) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 20=f407desc7IntegerLeftProduct 0 20) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 21=f407desc7IntegerLeftProduct 0 21) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 22=f407desc7IntegerLeftProduct 0 22) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 23=f407desc7IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f407desc7_left_row0_columns2

private theorem f407desc7_left_row0_columns3 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 24=f407desc7IntegerLeftProduct 0 24) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 25=f407desc7IntegerLeftProduct 0 25) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 26=f407desc7IntegerLeftProduct 0 26) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 27=f407desc7IntegerLeftProduct 0 27) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 28=f407desc7IntegerLeftProduct 0 28) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 29=f407desc7IntegerLeftProduct 0 29) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 30=f407desc7IntegerLeftProduct 0 30) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 31=f407desc7IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f407desc7_left_row0_columns3

private theorem f407desc7_left_row0_columns4 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 32=f407desc7IntegerLeftProduct 0 32) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 33=f407desc7IntegerLeftProduct 0 33) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 34=f407desc7IntegerLeftProduct 0 34) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 35=f407desc7IntegerLeftProduct 0 35) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 36=f407desc7IntegerLeftProduct 0 36) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 37=f407desc7IntegerLeftProduct 0 37) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 38=f407desc7IntegerLeftProduct 0 38) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 39=f407desc7IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f407desc7_left_row0_columns4

private theorem f407desc7_left_row0_columns5 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 40=f407desc7IntegerLeftProduct 0 40) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 41=f407desc7IntegerLeftProduct 0 41) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 42=f407desc7IntegerLeftProduct 0 42) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 43=f407desc7IntegerLeftProduct 0 43) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 44=f407desc7IntegerLeftProduct 0 44) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 45=f407desc7IntegerLeftProduct 0 45) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 0 46=f407desc7IntegerLeftProduct 0 46) := by
  decide +kernel

#print axioms f407desc7_left_row0_columns5

private theorem f407desc7_left_row1_columns0 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 0=f407desc7IntegerLeftProduct 1 0) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 1=f407desc7IntegerLeftProduct 1 1) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 2=f407desc7IntegerLeftProduct 1 2) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 3=f407desc7IntegerLeftProduct 1 3) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 4=f407desc7IntegerLeftProduct 1 4) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 5=f407desc7IntegerLeftProduct 1 5) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 6=f407desc7IntegerLeftProduct 1 6) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 7=f407desc7IntegerLeftProduct 1 7) := by
  decide +kernel

#print axioms f407desc7_left_row1_columns0

private theorem f407desc7_left_row1_columns1 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 8=f407desc7IntegerLeftProduct 1 8) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 9=f407desc7IntegerLeftProduct 1 9) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 10=f407desc7IntegerLeftProduct 1 10) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 11=f407desc7IntegerLeftProduct 1 11) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 12=f407desc7IntegerLeftProduct 1 12) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 13=f407desc7IntegerLeftProduct 1 13) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 14=f407desc7IntegerLeftProduct 1 14) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 15=f407desc7IntegerLeftProduct 1 15) := by
  decide +kernel

#print axioms f407desc7_left_row1_columns1

private theorem f407desc7_left_row1_columns2 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 16=f407desc7IntegerLeftProduct 1 16) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 17=f407desc7IntegerLeftProduct 1 17) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 18=f407desc7IntegerLeftProduct 1 18) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 19=f407desc7IntegerLeftProduct 1 19) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 20=f407desc7IntegerLeftProduct 1 20) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 21=f407desc7IntegerLeftProduct 1 21) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 22=f407desc7IntegerLeftProduct 1 22) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 23=f407desc7IntegerLeftProduct 1 23) := by
  decide +kernel

#print axioms f407desc7_left_row1_columns2

private theorem f407desc7_left_row1_columns3 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 24=f407desc7IntegerLeftProduct 1 24) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 25=f407desc7IntegerLeftProduct 1 25) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 26=f407desc7IntegerLeftProduct 1 26) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 27=f407desc7IntegerLeftProduct 1 27) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 28=f407desc7IntegerLeftProduct 1 28) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 29=f407desc7IntegerLeftProduct 1 29) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 30=f407desc7IntegerLeftProduct 1 30) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 31=f407desc7IntegerLeftProduct 1 31) := by
  decide +kernel

#print axioms f407desc7_left_row1_columns3

private theorem f407desc7_left_row1_columns4 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 32=f407desc7IntegerLeftProduct 1 32) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 33=f407desc7IntegerLeftProduct 1 33) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 34=f407desc7IntegerLeftProduct 1 34) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 35=f407desc7IntegerLeftProduct 1 35) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 36=f407desc7IntegerLeftProduct 1 36) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 37=f407desc7IntegerLeftProduct 1 37) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 38=f407desc7IntegerLeftProduct 1 38) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 39=f407desc7IntegerLeftProduct 1 39) := by
  decide +kernel

#print axioms f407desc7_left_row1_columns4

private theorem f407desc7_left_row1_columns5 :
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 40=f407desc7IntegerLeftProduct 1 40) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 41=f407desc7IntegerLeftProduct 1 41) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 42=f407desc7IntegerLeftProduct 1 42) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 43=f407desc7IntegerLeftProduct 1 43) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 44=f407desc7IntegerLeftProduct 1 44) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 45=f407desc7IntegerLeftProduct 1 45) ∧
    ((f407desc7IntegerCoordinatesᵀ*f414rawInteger) 1 46=f407desc7IntegerLeftProduct 1 46) := by
  decide +kernel

#print axioms f407desc7_left_row1_columns5

theorem f407desc7_compression_check :
    f407desc7ᵀ*f414rawM4Form*f407desc7=f407desc7Form := by
  have hD := f407desc7_coordinates_decode
  have hV : f407desc7IntegerCoordinatesᵀ*f414rawInteger=f407desc7IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f407desc7_left_row0_columns0.1
      · exact f407desc7_left_row0_columns0.2.1
      · exact f407desc7_left_row0_columns0.2.2.1
      · exact f407desc7_left_row0_columns0.2.2.2.1
      · exact f407desc7_left_row0_columns0.2.2.2.2.1
      · exact f407desc7_left_row0_columns0.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns0.2.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns0.2.2.2.2.2.2.2
      · exact f407desc7_left_row0_columns1.1
      · exact f407desc7_left_row0_columns1.2.1
      · exact f407desc7_left_row0_columns1.2.2.1
      · exact f407desc7_left_row0_columns1.2.2.2.1
      · exact f407desc7_left_row0_columns1.2.2.2.2.1
      · exact f407desc7_left_row0_columns1.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns1.2.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns1.2.2.2.2.2.2.2
      · exact f407desc7_left_row0_columns2.1
      · exact f407desc7_left_row0_columns2.2.1
      · exact f407desc7_left_row0_columns2.2.2.1
      · exact f407desc7_left_row0_columns2.2.2.2.1
      · exact f407desc7_left_row0_columns2.2.2.2.2.1
      · exact f407desc7_left_row0_columns2.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns2.2.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns2.2.2.2.2.2.2.2
      · exact f407desc7_left_row0_columns3.1
      · exact f407desc7_left_row0_columns3.2.1
      · exact f407desc7_left_row0_columns3.2.2.1
      · exact f407desc7_left_row0_columns3.2.2.2.1
      · exact f407desc7_left_row0_columns3.2.2.2.2.1
      · exact f407desc7_left_row0_columns3.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns3.2.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns3.2.2.2.2.2.2.2
      · exact f407desc7_left_row0_columns4.1
      · exact f407desc7_left_row0_columns4.2.1
      · exact f407desc7_left_row0_columns4.2.2.1
      · exact f407desc7_left_row0_columns4.2.2.2.1
      · exact f407desc7_left_row0_columns4.2.2.2.2.1
      · exact f407desc7_left_row0_columns4.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns4.2.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns4.2.2.2.2.2.2.2
      · exact f407desc7_left_row0_columns5.1
      · exact f407desc7_left_row0_columns5.2.1
      · exact f407desc7_left_row0_columns5.2.2.1
      · exact f407desc7_left_row0_columns5.2.2.2.1
      · exact f407desc7_left_row0_columns5.2.2.2.2.1
      · exact f407desc7_left_row0_columns5.2.2.2.2.2.1
      · exact f407desc7_left_row0_columns5.2.2.2.2.2.2
    · fin_cases b
      · exact f407desc7_left_row1_columns0.1
      · exact f407desc7_left_row1_columns0.2.1
      · exact f407desc7_left_row1_columns0.2.2.1
      · exact f407desc7_left_row1_columns0.2.2.2.1
      · exact f407desc7_left_row1_columns0.2.2.2.2.1
      · exact f407desc7_left_row1_columns0.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns0.2.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns0.2.2.2.2.2.2.2
      · exact f407desc7_left_row1_columns1.1
      · exact f407desc7_left_row1_columns1.2.1
      · exact f407desc7_left_row1_columns1.2.2.1
      · exact f407desc7_left_row1_columns1.2.2.2.1
      · exact f407desc7_left_row1_columns1.2.2.2.2.1
      · exact f407desc7_left_row1_columns1.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns1.2.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns1.2.2.2.2.2.2.2
      · exact f407desc7_left_row1_columns2.1
      · exact f407desc7_left_row1_columns2.2.1
      · exact f407desc7_left_row1_columns2.2.2.1
      · exact f407desc7_left_row1_columns2.2.2.2.1
      · exact f407desc7_left_row1_columns2.2.2.2.2.1
      · exact f407desc7_left_row1_columns2.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns2.2.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns2.2.2.2.2.2.2.2
      · exact f407desc7_left_row1_columns3.1
      · exact f407desc7_left_row1_columns3.2.1
      · exact f407desc7_left_row1_columns3.2.2.1
      · exact f407desc7_left_row1_columns3.2.2.2.1
      · exact f407desc7_left_row1_columns3.2.2.2.2.1
      · exact f407desc7_left_row1_columns3.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns3.2.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns3.2.2.2.2.2.2.2
      · exact f407desc7_left_row1_columns4.1
      · exact f407desc7_left_row1_columns4.2.1
      · exact f407desc7_left_row1_columns4.2.2.1
      · exact f407desc7_left_row1_columns4.2.2.2.1
      · exact f407desc7_left_row1_columns4.2.2.2.2.1
      · exact f407desc7_left_row1_columns4.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns4.2.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns4.2.2.2.2.2.2.2
      · exact f407desc7_left_row1_columns5.1
      · exact f407desc7_left_row1_columns5.2.1
      · exact f407desc7_left_row1_columns5.2.2.1
      · exact f407desc7_left_row1_columns5.2.2.2.1
      · exact f407desc7_left_row1_columns5.2.2.2.2.1
      · exact f407desc7_left_row1_columns5.2.2.2.2.2.1
      · exact f407desc7_left_row1_columns5.2.2.2.2.2.2
  have hY : f407desc7IntegerLeftProduct*f407desc7IntegerCoordinates=f407desc7IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc7IntegerLeftProduct*f407desc7IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc7IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc7IntegerLeftProduct*f407desc7IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc7IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc7IntegerForm=f407desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc7IntegerForm) (f407desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f414rawInteger f407desc7IntegerCoordinates f407desc7IntegerLeftProduct f407desc7IntegerForm
    f414rawM4Form f407desc7 f407desc7Form f414_raw_integer_check hD hV hY hF

theorem f407desc7_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f407basis b407relative
    f414basis f407desc7 f414rawM4Form f407desc7Form
    f407desc7_actual f414_actual_raw_M4_matrix f407desc7_compression_check x y


#print axioms f407desc7_compression_check
#print axioms f407desc7_source_form
end TorusLean.BosonFiniteCertificate
