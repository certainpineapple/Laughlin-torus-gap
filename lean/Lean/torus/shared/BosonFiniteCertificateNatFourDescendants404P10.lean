import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
import torus.shared.BosonFiniteCertificateNatFourRaise404
import torus.shared.BosonFiniteCertificateNatFourRaise405
import torus.shared.BosonFiniteCertificateNatFourRaise406
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate404

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

def f404desc10Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(3462108766797836566092344144931/19531250000000000000), (6770336048868575927993813045019/19531250000000000000);
    (6770336048868575927993813045019/19531250000000000000), (3511453052919353058225378942723/3906250000000000000)]

private def f404desc10IntegerCoordinates : Matrix (Fin 47) (Fin 2) ℤ :=
  !![1, (-1);
    26, (-26);
    101, (-95);
    236, (-176);
    383, (-113);
    486, 234;
    537, 723;
    276, 480;
    190, (-196);
    1200, (-1212);
    2192, (-1772);
    2740, (-400);
    2844, 3276;
    2880, 6696;
    1446, (-1560);
    3760, (-3820);
    3510, (-1170);
    3744, 3240;
    2100, 2688;
    1740, (-3000);
    4560, (-10320);
    8064, (-15624);
    5670, (-15750);
    8316, (-22176);
    360, (-408);
    2340, (-2916);
    2200, (-2440);
    450, 3060;
    (-720), 11088;
    (-420), 7476;
    1860, (-4620);
    (-7920), (-540);
    (-17280), 18360;
    (-15120), 32256;
    (-12960), 2880;
    (-16800), (-5880);
    (-1008), (-9072);
    8820, (-31500);
    (-3510), 0;
    (-28080), 14400;
    (-23940), 22680;
    (-6804), 11340;
    (-28560), 18480;
    20160, (-2520);
    15750, (-9450);
    10080, 0;
    44100, (-12600)]

private def f404desc10IntegerLeftProduct : Matrix (Fin 2) (Fin 47) ℤ :=
  !![0, 0, 0, 0, 0, 0, 454558426613756425918201688064000, 975250567674917397368109693849600, 0, 0, 0, 0, 1927283218117613435151636480000, 226288670441730734174410637798400, 0, 0, (-1689412838170940259249154867200), 8337070735019289270334556006400, 71811333892087576595944872192000, (-83765358130478131155531571200), (-24073369174575195408122112000), 5592040825915581314030292326400, (-6605175620368222520475359462400), 0, 0, 0, 0, (-248713825669609273101280051200), 3675859823947370416664178816000, 75967865909942515237063007539200, 0, 134595317190743349992264908800, 2064441228443617752991933977600, 3243215753756276391943138483200, (-8559069903851040703131669273600), (-2244031192329851805238660838400), 0, 0, (-1087743019989366155007813427200), (-1809344395160928901061235993600), (-6671122273416626047884882355200), 0, 38847226781049589438970112000, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1109136756485157775805581722316800, 2049076148450319563042632672972800, 0, 0, 0, 0, 3738929581045586562015415910400, 525855492249539796566836566451200, 0, 0, (-3277460913960196889839304294400), 23239198602233691181155900979200, 182822686865259532968631843584000, (-162504753694117605468188467200), 3350664639930129197493839616000, 28711818693353551282762326681600, (-25854224790357376562926920268800), 0, 0, 0, 0, (-482504682105123919122102681600), 12907295315549299198766590848000, 207786466642518737813571968102400, 0, 261115011438476507460487987200, 9163466754489346797083782425600, 23110243717682434819400396928000, (-15094410962129793309378738816000), (-2618370143275049440990463462400), 0, 0, (-2110221455284002350328037171200), 1050294439113816272600514124800, (-20701835007575768326822455475200), 0, 8135594615177675258475931084800, 0, 0, 0, 0]

private def f404desc10IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1595339719740443089655352181984204800, 3119770851318639787619549051144755200;
    3119770851318639787619549051144755200, 8090387833926189446151273084033792000]

private theorem f404desc10_coordinates_decode : natFourIntegerMatrix 3 f404desc10IntegerCoordinates=f404desc10 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc10IntegerCoordinates) (f404desc10) (by decide +kernel) a b

#print axioms f404desc10_coordinates_decode

private theorem f404desc10_left_row0_columns0 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 0=f404desc10IntegerLeftProduct 0 0) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 1=f404desc10IntegerLeftProduct 0 1) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 2=f404desc10IntegerLeftProduct 0 2) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 3=f404desc10IntegerLeftProduct 0 3) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 4=f404desc10IntegerLeftProduct 0 4) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 5=f404desc10IntegerLeftProduct 0 5) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 6=f404desc10IntegerLeftProduct 0 6) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 7=f404desc10IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f404desc10_left_row0_columns0

private theorem f404desc10_left_row0_columns1 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 8=f404desc10IntegerLeftProduct 0 8) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 9=f404desc10IntegerLeftProduct 0 9) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 10=f404desc10IntegerLeftProduct 0 10) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 11=f404desc10IntegerLeftProduct 0 11) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 12=f404desc10IntegerLeftProduct 0 12) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 13=f404desc10IntegerLeftProduct 0 13) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 14=f404desc10IntegerLeftProduct 0 14) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 15=f404desc10IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f404desc10_left_row0_columns1

private theorem f404desc10_left_row0_columns2 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 16=f404desc10IntegerLeftProduct 0 16) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 17=f404desc10IntegerLeftProduct 0 17) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 18=f404desc10IntegerLeftProduct 0 18) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 19=f404desc10IntegerLeftProduct 0 19) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 20=f404desc10IntegerLeftProduct 0 20) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 21=f404desc10IntegerLeftProduct 0 21) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 22=f404desc10IntegerLeftProduct 0 22) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 23=f404desc10IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f404desc10_left_row0_columns2

private theorem f404desc10_left_row0_columns3 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 24=f404desc10IntegerLeftProduct 0 24) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 25=f404desc10IntegerLeftProduct 0 25) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 26=f404desc10IntegerLeftProduct 0 26) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 27=f404desc10IntegerLeftProduct 0 27) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 28=f404desc10IntegerLeftProduct 0 28) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 29=f404desc10IntegerLeftProduct 0 29) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 30=f404desc10IntegerLeftProduct 0 30) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 31=f404desc10IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f404desc10_left_row0_columns3

private theorem f404desc10_left_row0_columns4 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 32=f404desc10IntegerLeftProduct 0 32) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 33=f404desc10IntegerLeftProduct 0 33) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 34=f404desc10IntegerLeftProduct 0 34) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 35=f404desc10IntegerLeftProduct 0 35) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 36=f404desc10IntegerLeftProduct 0 36) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 37=f404desc10IntegerLeftProduct 0 37) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 38=f404desc10IntegerLeftProduct 0 38) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 39=f404desc10IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f404desc10_left_row0_columns4

private theorem f404desc10_left_row0_columns5 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 40=f404desc10IntegerLeftProduct 0 40) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 41=f404desc10IntegerLeftProduct 0 41) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 42=f404desc10IntegerLeftProduct 0 42) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 43=f404desc10IntegerLeftProduct 0 43) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 44=f404desc10IntegerLeftProduct 0 44) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 45=f404desc10IntegerLeftProduct 0 45) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 0 46=f404desc10IntegerLeftProduct 0 46) := by
  decide +kernel

#print axioms f404desc10_left_row0_columns5

private theorem f404desc10_left_row1_columns0 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 0=f404desc10IntegerLeftProduct 1 0) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 1=f404desc10IntegerLeftProduct 1 1) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 2=f404desc10IntegerLeftProduct 1 2) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 3=f404desc10IntegerLeftProduct 1 3) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 4=f404desc10IntegerLeftProduct 1 4) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 5=f404desc10IntegerLeftProduct 1 5) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 6=f404desc10IntegerLeftProduct 1 6) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 7=f404desc10IntegerLeftProduct 1 7) := by
  decide +kernel

#print axioms f404desc10_left_row1_columns0

private theorem f404desc10_left_row1_columns1 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 8=f404desc10IntegerLeftProduct 1 8) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 9=f404desc10IntegerLeftProduct 1 9) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 10=f404desc10IntegerLeftProduct 1 10) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 11=f404desc10IntegerLeftProduct 1 11) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 12=f404desc10IntegerLeftProduct 1 12) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 13=f404desc10IntegerLeftProduct 1 13) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 14=f404desc10IntegerLeftProduct 1 14) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 15=f404desc10IntegerLeftProduct 1 15) := by
  decide +kernel

#print axioms f404desc10_left_row1_columns1

private theorem f404desc10_left_row1_columns2 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 16=f404desc10IntegerLeftProduct 1 16) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 17=f404desc10IntegerLeftProduct 1 17) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 18=f404desc10IntegerLeftProduct 1 18) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 19=f404desc10IntegerLeftProduct 1 19) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 20=f404desc10IntegerLeftProduct 1 20) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 21=f404desc10IntegerLeftProduct 1 21) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 22=f404desc10IntegerLeftProduct 1 22) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 23=f404desc10IntegerLeftProduct 1 23) := by
  decide +kernel

#print axioms f404desc10_left_row1_columns2

private theorem f404desc10_left_row1_columns3 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 24=f404desc10IntegerLeftProduct 1 24) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 25=f404desc10IntegerLeftProduct 1 25) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 26=f404desc10IntegerLeftProduct 1 26) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 27=f404desc10IntegerLeftProduct 1 27) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 28=f404desc10IntegerLeftProduct 1 28) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 29=f404desc10IntegerLeftProduct 1 29) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 30=f404desc10IntegerLeftProduct 1 30) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 31=f404desc10IntegerLeftProduct 1 31) := by
  decide +kernel

#print axioms f404desc10_left_row1_columns3

private theorem f404desc10_left_row1_columns4 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 32=f404desc10IntegerLeftProduct 1 32) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 33=f404desc10IntegerLeftProduct 1 33) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 34=f404desc10IntegerLeftProduct 1 34) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 35=f404desc10IntegerLeftProduct 1 35) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 36=f404desc10IntegerLeftProduct 1 36) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 37=f404desc10IntegerLeftProduct 1 37) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 38=f404desc10IntegerLeftProduct 1 38) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 39=f404desc10IntegerLeftProduct 1 39) := by
  decide +kernel

#print axioms f404desc10_left_row1_columns4

private theorem f404desc10_left_row1_columns5 :
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 40=f404desc10IntegerLeftProduct 1 40) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 41=f404desc10IntegerLeftProduct 1 41) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 42=f404desc10IntegerLeftProduct 1 42) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 43=f404desc10IntegerLeftProduct 1 43) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 44=f404desc10IntegerLeftProduct 1 44) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 45=f404desc10IntegerLeftProduct 1 45) ∧
    ((f404desc10IntegerCoordinatesᵀ*f414rawInteger) 1 46=f404desc10IntegerLeftProduct 1 46) := by
  decide +kernel

#print axioms f404desc10_left_row1_columns5

theorem f404desc10_compression_check :
    f404desc10ᵀ*f414rawM4Form*f404desc10=f404desc10Form := by
  have hD := f404desc10_coordinates_decode
  have hV : f404desc10IntegerCoordinatesᵀ*f414rawInteger=f404desc10IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f404desc10_left_row0_columns0.1
      · exact f404desc10_left_row0_columns0.2.1
      · exact f404desc10_left_row0_columns0.2.2.1
      · exact f404desc10_left_row0_columns0.2.2.2.1
      · exact f404desc10_left_row0_columns0.2.2.2.2.1
      · exact f404desc10_left_row0_columns0.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns0.2.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns0.2.2.2.2.2.2.2
      · exact f404desc10_left_row0_columns1.1
      · exact f404desc10_left_row0_columns1.2.1
      · exact f404desc10_left_row0_columns1.2.2.1
      · exact f404desc10_left_row0_columns1.2.2.2.1
      · exact f404desc10_left_row0_columns1.2.2.2.2.1
      · exact f404desc10_left_row0_columns1.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns1.2.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns1.2.2.2.2.2.2.2
      · exact f404desc10_left_row0_columns2.1
      · exact f404desc10_left_row0_columns2.2.1
      · exact f404desc10_left_row0_columns2.2.2.1
      · exact f404desc10_left_row0_columns2.2.2.2.1
      · exact f404desc10_left_row0_columns2.2.2.2.2.1
      · exact f404desc10_left_row0_columns2.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns2.2.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns2.2.2.2.2.2.2.2
      · exact f404desc10_left_row0_columns3.1
      · exact f404desc10_left_row0_columns3.2.1
      · exact f404desc10_left_row0_columns3.2.2.1
      · exact f404desc10_left_row0_columns3.2.2.2.1
      · exact f404desc10_left_row0_columns3.2.2.2.2.1
      · exact f404desc10_left_row0_columns3.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns3.2.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns3.2.2.2.2.2.2.2
      · exact f404desc10_left_row0_columns4.1
      · exact f404desc10_left_row0_columns4.2.1
      · exact f404desc10_left_row0_columns4.2.2.1
      · exact f404desc10_left_row0_columns4.2.2.2.1
      · exact f404desc10_left_row0_columns4.2.2.2.2.1
      · exact f404desc10_left_row0_columns4.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns4.2.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns4.2.2.2.2.2.2.2
      · exact f404desc10_left_row0_columns5.1
      · exact f404desc10_left_row0_columns5.2.1
      · exact f404desc10_left_row0_columns5.2.2.1
      · exact f404desc10_left_row0_columns5.2.2.2.1
      · exact f404desc10_left_row0_columns5.2.2.2.2.1
      · exact f404desc10_left_row0_columns5.2.2.2.2.2.1
      · exact f404desc10_left_row0_columns5.2.2.2.2.2.2
    · fin_cases b
      · exact f404desc10_left_row1_columns0.1
      · exact f404desc10_left_row1_columns0.2.1
      · exact f404desc10_left_row1_columns0.2.2.1
      · exact f404desc10_left_row1_columns0.2.2.2.1
      · exact f404desc10_left_row1_columns0.2.2.2.2.1
      · exact f404desc10_left_row1_columns0.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns0.2.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns0.2.2.2.2.2.2.2
      · exact f404desc10_left_row1_columns1.1
      · exact f404desc10_left_row1_columns1.2.1
      · exact f404desc10_left_row1_columns1.2.2.1
      · exact f404desc10_left_row1_columns1.2.2.2.1
      · exact f404desc10_left_row1_columns1.2.2.2.2.1
      · exact f404desc10_left_row1_columns1.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns1.2.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns1.2.2.2.2.2.2.2
      · exact f404desc10_left_row1_columns2.1
      · exact f404desc10_left_row1_columns2.2.1
      · exact f404desc10_left_row1_columns2.2.2.1
      · exact f404desc10_left_row1_columns2.2.2.2.1
      · exact f404desc10_left_row1_columns2.2.2.2.2.1
      · exact f404desc10_left_row1_columns2.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns2.2.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns2.2.2.2.2.2.2.2
      · exact f404desc10_left_row1_columns3.1
      · exact f404desc10_left_row1_columns3.2.1
      · exact f404desc10_left_row1_columns3.2.2.1
      · exact f404desc10_left_row1_columns3.2.2.2.1
      · exact f404desc10_left_row1_columns3.2.2.2.2.1
      · exact f404desc10_left_row1_columns3.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns3.2.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns3.2.2.2.2.2.2.2
      · exact f404desc10_left_row1_columns4.1
      · exact f404desc10_left_row1_columns4.2.1
      · exact f404desc10_left_row1_columns4.2.2.1
      · exact f404desc10_left_row1_columns4.2.2.2.1
      · exact f404desc10_left_row1_columns4.2.2.2.2.1
      · exact f404desc10_left_row1_columns4.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns4.2.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns4.2.2.2.2.2.2.2
      · exact f404desc10_left_row1_columns5.1
      · exact f404desc10_left_row1_columns5.2.1
      · exact f404desc10_left_row1_columns5.2.2.1
      · exact f404desc10_left_row1_columns5.2.2.2.1
      · exact f404desc10_left_row1_columns5.2.2.2.2.1
      · exact f404desc10_left_row1_columns5.2.2.2.2.2.1
      · exact f404desc10_left_row1_columns5.2.2.2.2.2.2
  have hY : f404desc10IntegerLeftProduct*f404desc10IntegerCoordinates=f404desc10IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc10IntegerLeftProduct*f404desc10IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc10IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc10IntegerLeftProduct*f404desc10IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc10IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc10IntegerForm=f404desc10Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc10IntegerForm) (f404desc10Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f414rawInteger f404desc10IntegerCoordinates f404desc10IntegerLeftProduct f404desc10IntegerForm
    f414rawM4Form f404desc10 f404desc10Form f414_raw_integer_check hD hV hY hF

theorem f404desc10_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc10Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 10
    f404basis b404relative
    f414basis f404desc10 f414rawM4Form f404desc10Form
    f404desc10_actual f414_actual_raw_M4_matrix f404desc10_compression_check x y


#print axioms f404desc10_compression_check
#print axioms f404desc10_source_form
end TorusLean.BosonFiniteCertificate
