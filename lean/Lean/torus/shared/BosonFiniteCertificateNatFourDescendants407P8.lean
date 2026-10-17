import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
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

def f407desc8Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1713781589754699299214259492977/15625000000000000000000), (603139568795352329684053570551/3906250000000000000000);
    (603139568795352329684053570551/3906250000000000000000), (219894034284300236966801158113/976562500000000000000)]

private def f407desc8IntegerCoordinates : Matrix (Fin 54) (Fin 2) ℤ :=
  !![3, (-4);
    51, (-68);
    111, (-128);
    117, (-16);
    75, 280;
    33, 376;
    (-99), 12;
    (-297), (-444);
    204, (-292);
    414, (-592);
    (-168), 864;
    (-126), 2208;
    456, 1032;
    (-390), (-1480);
    (-696), (-1312);
    (-468), 284;
    (-2568), 2104;
    (-1230), 400;
    (-846), (-1152);
    (-4272), 976;
    (-1620), (-880);
    (-1050), (-6080);
    (-3504), 2432;
    (-3528), 5544;
    (-30), (-280);
    (-756), 17808;
    504, 4648;
    120, (-260);
    (-720), 280;
    (-1056), 2168;
    2640, 700;
    5148, (-2124);
    2640, (-2000);
    (-3276), 2468;
    0, (-720);
    15570, (-12880);
    8352, (-1376);
    (-2520), 7000;
    7260, (-12560);
    18480, (-32960);
    0, (-7840);
    10710, (-24360);
    13104, (-27832);
    (-1260), 940;
    3780, (-2180);
    (-720), 8040;
    (-23184), 35672;
    (-4560), 8640;
    (-40320), 44240;
    (-26208), 25424;
    3150, (-20720);
    (-8400), 13440;
    12600, (-2240);
    28350, (-25200)]

private def f407desc8IntegerLeftProduct : Matrix (Fin 2) (Fin 54) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, (-605971385823454060528374009062400), 0, 0, 0, 0, 0, (-7194463089315980624700851404800), (-199411893953274004671772689868800), 0, 0, 0, 988367069470135078806185779200, (-26613464399458718723788942771200), 0, (-127598537097251641051493990400), 6314718419587615773864660940800, 0, (-5317393257366518865289490841600), 0, 0, 0, 0, 0, 0, 1222570594125389600762543308800, (-23353469240862045267408456576000), 0, 0, (-445594756941493568509221273600), 5831215228547083368427412966400, 0, 521475254954192068402063564800, (-130372628161048838470810598400), 0, 0, 0, 0, (-30724489545304381012021248000), (-3873870977798254700288544768000), 0, 1796652842447747731967383449600, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, (-893129656326650963426224321228800), 0, 0, 0, 0, 0, (-16203227600491128263949719961600), (-281704568624024332566289034649600), 0, 0, 0, 2225980834305652657450841702400, (-33536616988036249890701963366400), 0, (-287374902902351966568377548800), 7917312721654248186798061977600, 0, (-6807766553261429587840486195200), 0, 0, 0, 0, 0, 0, 2753449397220737530627316121600, (-29713851586817666932241604096000), 0, 0, (-1003559696625441215236748083200), 7048291701972465776058322636800, 0, 1174456283293297128424933785600, (-340769268990326838050042572800), 0, 0, 0, 0, (-69197073344876993419911168000), (-5032555689890692207250141184000), 0, 2303462614062192953280041779200, 0, 0, 0, 0, 0, 0]

private def f407desc8IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![394855278279482718538965387181900800, 555853426601796707036823770619801600;
    555853426601796707036823770619801600, 810617367985644393554415789267763200]

private theorem f407desc8_coordinates_decode : natFourIntegerMatrix 60 f407desc8IntegerCoordinates=f407desc8 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc8IntegerCoordinates) (f407desc8) (by decide +kernel) a b

#print axioms f407desc8_coordinates_decode

private theorem f407desc8_left_row0_columns0 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 0=f407desc8IntegerLeftProduct 0 0) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 1=f407desc8IntegerLeftProduct 0 1) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 2=f407desc8IntegerLeftProduct 0 2) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 3=f407desc8IntegerLeftProduct 0 3) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 4=f407desc8IntegerLeftProduct 0 4) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 5=f407desc8IntegerLeftProduct 0 5) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 6=f407desc8IntegerLeftProduct 0 6) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 7=f407desc8IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f407desc8_left_row0_columns0

private theorem f407desc8_left_row0_columns1 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 8=f407desc8IntegerLeftProduct 0 8) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 9=f407desc8IntegerLeftProduct 0 9) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 10=f407desc8IntegerLeftProduct 0 10) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 11=f407desc8IntegerLeftProduct 0 11) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 12=f407desc8IntegerLeftProduct 0 12) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 13=f407desc8IntegerLeftProduct 0 13) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 14=f407desc8IntegerLeftProduct 0 14) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 15=f407desc8IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f407desc8_left_row0_columns1

private theorem f407desc8_left_row0_columns2 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 16=f407desc8IntegerLeftProduct 0 16) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 17=f407desc8IntegerLeftProduct 0 17) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 18=f407desc8IntegerLeftProduct 0 18) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 19=f407desc8IntegerLeftProduct 0 19) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 20=f407desc8IntegerLeftProduct 0 20) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 21=f407desc8IntegerLeftProduct 0 21) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 22=f407desc8IntegerLeftProduct 0 22) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 23=f407desc8IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f407desc8_left_row0_columns2

private theorem f407desc8_left_row0_columns3 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 24=f407desc8IntegerLeftProduct 0 24) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 25=f407desc8IntegerLeftProduct 0 25) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 26=f407desc8IntegerLeftProduct 0 26) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 27=f407desc8IntegerLeftProduct 0 27) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 28=f407desc8IntegerLeftProduct 0 28) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 29=f407desc8IntegerLeftProduct 0 29) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 30=f407desc8IntegerLeftProduct 0 30) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 31=f407desc8IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f407desc8_left_row0_columns3

private theorem f407desc8_left_row0_columns4 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 32=f407desc8IntegerLeftProduct 0 32) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 33=f407desc8IntegerLeftProduct 0 33) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 34=f407desc8IntegerLeftProduct 0 34) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 35=f407desc8IntegerLeftProduct 0 35) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 36=f407desc8IntegerLeftProduct 0 36) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 37=f407desc8IntegerLeftProduct 0 37) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 38=f407desc8IntegerLeftProduct 0 38) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 39=f407desc8IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f407desc8_left_row0_columns4

private theorem f407desc8_left_row0_columns5 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 40=f407desc8IntegerLeftProduct 0 40) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 41=f407desc8IntegerLeftProduct 0 41) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 42=f407desc8IntegerLeftProduct 0 42) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 43=f407desc8IntegerLeftProduct 0 43) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 44=f407desc8IntegerLeftProduct 0 44) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 45=f407desc8IntegerLeftProduct 0 45) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 46=f407desc8IntegerLeftProduct 0 46) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 47=f407desc8IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f407desc8_left_row0_columns5

private theorem f407desc8_left_row0_columns6 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 48=f407desc8IntegerLeftProduct 0 48) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 49=f407desc8IntegerLeftProduct 0 49) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 50=f407desc8IntegerLeftProduct 0 50) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 51=f407desc8IntegerLeftProduct 0 51) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 52=f407desc8IntegerLeftProduct 0 52) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 0 53=f407desc8IntegerLeftProduct 0 53) := by
  decide +kernel

#print axioms f407desc8_left_row0_columns6

private theorem f407desc8_left_row1_columns0 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 0=f407desc8IntegerLeftProduct 1 0) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 1=f407desc8IntegerLeftProduct 1 1) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 2=f407desc8IntegerLeftProduct 1 2) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 3=f407desc8IntegerLeftProduct 1 3) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 4=f407desc8IntegerLeftProduct 1 4) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 5=f407desc8IntegerLeftProduct 1 5) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 6=f407desc8IntegerLeftProduct 1 6) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 7=f407desc8IntegerLeftProduct 1 7) := by
  decide +kernel

#print axioms f407desc8_left_row1_columns0

private theorem f407desc8_left_row1_columns1 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 8=f407desc8IntegerLeftProduct 1 8) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 9=f407desc8IntegerLeftProduct 1 9) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 10=f407desc8IntegerLeftProduct 1 10) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 11=f407desc8IntegerLeftProduct 1 11) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 12=f407desc8IntegerLeftProduct 1 12) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 13=f407desc8IntegerLeftProduct 1 13) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 14=f407desc8IntegerLeftProduct 1 14) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 15=f407desc8IntegerLeftProduct 1 15) := by
  decide +kernel

#print axioms f407desc8_left_row1_columns1

private theorem f407desc8_left_row1_columns2 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 16=f407desc8IntegerLeftProduct 1 16) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 17=f407desc8IntegerLeftProduct 1 17) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 18=f407desc8IntegerLeftProduct 1 18) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 19=f407desc8IntegerLeftProduct 1 19) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 20=f407desc8IntegerLeftProduct 1 20) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 21=f407desc8IntegerLeftProduct 1 21) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 22=f407desc8IntegerLeftProduct 1 22) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 23=f407desc8IntegerLeftProduct 1 23) := by
  decide +kernel

#print axioms f407desc8_left_row1_columns2

private theorem f407desc8_left_row1_columns3 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 24=f407desc8IntegerLeftProduct 1 24) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 25=f407desc8IntegerLeftProduct 1 25) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 26=f407desc8IntegerLeftProduct 1 26) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 27=f407desc8IntegerLeftProduct 1 27) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 28=f407desc8IntegerLeftProduct 1 28) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 29=f407desc8IntegerLeftProduct 1 29) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 30=f407desc8IntegerLeftProduct 1 30) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 31=f407desc8IntegerLeftProduct 1 31) := by
  decide +kernel

#print axioms f407desc8_left_row1_columns3

private theorem f407desc8_left_row1_columns4 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 32=f407desc8IntegerLeftProduct 1 32) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 33=f407desc8IntegerLeftProduct 1 33) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 34=f407desc8IntegerLeftProduct 1 34) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 35=f407desc8IntegerLeftProduct 1 35) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 36=f407desc8IntegerLeftProduct 1 36) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 37=f407desc8IntegerLeftProduct 1 37) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 38=f407desc8IntegerLeftProduct 1 38) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 39=f407desc8IntegerLeftProduct 1 39) := by
  decide +kernel

#print axioms f407desc8_left_row1_columns4

private theorem f407desc8_left_row1_columns5 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 40=f407desc8IntegerLeftProduct 1 40) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 41=f407desc8IntegerLeftProduct 1 41) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 42=f407desc8IntegerLeftProduct 1 42) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 43=f407desc8IntegerLeftProduct 1 43) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 44=f407desc8IntegerLeftProduct 1 44) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 45=f407desc8IntegerLeftProduct 1 45) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 46=f407desc8IntegerLeftProduct 1 46) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 47=f407desc8IntegerLeftProduct 1 47) := by
  decide +kernel

#print axioms f407desc8_left_row1_columns5

private theorem f407desc8_left_row1_columns6 :
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 48=f407desc8IntegerLeftProduct 1 48) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 49=f407desc8IntegerLeftProduct 1 49) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 50=f407desc8IntegerLeftProduct 1 50) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 51=f407desc8IntegerLeftProduct 1 51) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 52=f407desc8IntegerLeftProduct 1 52) ∧
    ((f407desc8IntegerCoordinatesᵀ*f415rawInteger) 1 53=f407desc8IntegerLeftProduct 1 53) := by
  decide +kernel

#print axioms f407desc8_left_row1_columns6

theorem f407desc8_compression_check :
    f407desc8ᵀ*f415rawM4Form*f407desc8=f407desc8Form := by
  have hD := f407desc8_coordinates_decode
  have hV : f407desc8IntegerCoordinatesᵀ*f415rawInteger=f407desc8IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f407desc8_left_row0_columns0.1
      · exact f407desc8_left_row0_columns0.2.1
      · exact f407desc8_left_row0_columns0.2.2.1
      · exact f407desc8_left_row0_columns0.2.2.2.1
      · exact f407desc8_left_row0_columns0.2.2.2.2.1
      · exact f407desc8_left_row0_columns0.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns0.2.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns0.2.2.2.2.2.2.2
      · exact f407desc8_left_row0_columns1.1
      · exact f407desc8_left_row0_columns1.2.1
      · exact f407desc8_left_row0_columns1.2.2.1
      · exact f407desc8_left_row0_columns1.2.2.2.1
      · exact f407desc8_left_row0_columns1.2.2.2.2.1
      · exact f407desc8_left_row0_columns1.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns1.2.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns1.2.2.2.2.2.2.2
      · exact f407desc8_left_row0_columns2.1
      · exact f407desc8_left_row0_columns2.2.1
      · exact f407desc8_left_row0_columns2.2.2.1
      · exact f407desc8_left_row0_columns2.2.2.2.1
      · exact f407desc8_left_row0_columns2.2.2.2.2.1
      · exact f407desc8_left_row0_columns2.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns2.2.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns2.2.2.2.2.2.2.2
      · exact f407desc8_left_row0_columns3.1
      · exact f407desc8_left_row0_columns3.2.1
      · exact f407desc8_left_row0_columns3.2.2.1
      · exact f407desc8_left_row0_columns3.2.2.2.1
      · exact f407desc8_left_row0_columns3.2.2.2.2.1
      · exact f407desc8_left_row0_columns3.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns3.2.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns3.2.2.2.2.2.2.2
      · exact f407desc8_left_row0_columns4.1
      · exact f407desc8_left_row0_columns4.2.1
      · exact f407desc8_left_row0_columns4.2.2.1
      · exact f407desc8_left_row0_columns4.2.2.2.1
      · exact f407desc8_left_row0_columns4.2.2.2.2.1
      · exact f407desc8_left_row0_columns4.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns4.2.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns4.2.2.2.2.2.2.2
      · exact f407desc8_left_row0_columns5.1
      · exact f407desc8_left_row0_columns5.2.1
      · exact f407desc8_left_row0_columns5.2.2.1
      · exact f407desc8_left_row0_columns5.2.2.2.1
      · exact f407desc8_left_row0_columns5.2.2.2.2.1
      · exact f407desc8_left_row0_columns5.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns5.2.2.2.2.2.2.1
      · exact f407desc8_left_row0_columns5.2.2.2.2.2.2.2
      · exact f407desc8_left_row0_columns6.1
      · exact f407desc8_left_row0_columns6.2.1
      · exact f407desc8_left_row0_columns6.2.2.1
      · exact f407desc8_left_row0_columns6.2.2.2.1
      · exact f407desc8_left_row0_columns6.2.2.2.2.1
      · exact f407desc8_left_row0_columns6.2.2.2.2.2
    · fin_cases b
      · exact f407desc8_left_row1_columns0.1
      · exact f407desc8_left_row1_columns0.2.1
      · exact f407desc8_left_row1_columns0.2.2.1
      · exact f407desc8_left_row1_columns0.2.2.2.1
      · exact f407desc8_left_row1_columns0.2.2.2.2.1
      · exact f407desc8_left_row1_columns0.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns0.2.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns0.2.2.2.2.2.2.2
      · exact f407desc8_left_row1_columns1.1
      · exact f407desc8_left_row1_columns1.2.1
      · exact f407desc8_left_row1_columns1.2.2.1
      · exact f407desc8_left_row1_columns1.2.2.2.1
      · exact f407desc8_left_row1_columns1.2.2.2.2.1
      · exact f407desc8_left_row1_columns1.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns1.2.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns1.2.2.2.2.2.2.2
      · exact f407desc8_left_row1_columns2.1
      · exact f407desc8_left_row1_columns2.2.1
      · exact f407desc8_left_row1_columns2.2.2.1
      · exact f407desc8_left_row1_columns2.2.2.2.1
      · exact f407desc8_left_row1_columns2.2.2.2.2.1
      · exact f407desc8_left_row1_columns2.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns2.2.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns2.2.2.2.2.2.2.2
      · exact f407desc8_left_row1_columns3.1
      · exact f407desc8_left_row1_columns3.2.1
      · exact f407desc8_left_row1_columns3.2.2.1
      · exact f407desc8_left_row1_columns3.2.2.2.1
      · exact f407desc8_left_row1_columns3.2.2.2.2.1
      · exact f407desc8_left_row1_columns3.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns3.2.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns3.2.2.2.2.2.2.2
      · exact f407desc8_left_row1_columns4.1
      · exact f407desc8_left_row1_columns4.2.1
      · exact f407desc8_left_row1_columns4.2.2.1
      · exact f407desc8_left_row1_columns4.2.2.2.1
      · exact f407desc8_left_row1_columns4.2.2.2.2.1
      · exact f407desc8_left_row1_columns4.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns4.2.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns4.2.2.2.2.2.2.2
      · exact f407desc8_left_row1_columns5.1
      · exact f407desc8_left_row1_columns5.2.1
      · exact f407desc8_left_row1_columns5.2.2.1
      · exact f407desc8_left_row1_columns5.2.2.2.1
      · exact f407desc8_left_row1_columns5.2.2.2.2.1
      · exact f407desc8_left_row1_columns5.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns5.2.2.2.2.2.2.1
      · exact f407desc8_left_row1_columns5.2.2.2.2.2.2.2
      · exact f407desc8_left_row1_columns6.1
      · exact f407desc8_left_row1_columns6.2.1
      · exact f407desc8_left_row1_columns6.2.2.1
      · exact f407desc8_left_row1_columns6.2.2.2.1
      · exact f407desc8_left_row1_columns6.2.2.2.2.1
      · exact f407desc8_left_row1_columns6.2.2.2.2.2
  have hY : f407desc8IntegerLeftProduct*f407desc8IntegerCoordinates=f407desc8IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc8IntegerLeftProduct*f407desc8IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc8IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc8IntegerLeftProduct*f407desc8IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc8IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc8IntegerForm=f407desc8Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc8IntegerForm) (f407desc8Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f415rawInteger f407desc8IntegerCoordinates f407desc8IntegerLeftProduct f407desc8IntegerForm
    f415rawM4Form f407desc8 f407desc8Form f415_raw_integer_check hD hV hY hF

theorem f407desc8_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc8Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 8
    f407basis b407relative
    f415basis f407desc8 f415rawM4Form f407desc8Form
    f407desc8_actual f415_actual_raw_M4_matrix f407desc8_compression_check x y


#print axioms f407desc8_compression_check
#print axioms f407desc8_source_form
end TorusLean.BosonFiniteCertificate
