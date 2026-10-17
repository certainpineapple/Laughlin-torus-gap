import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
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

def f404desc11Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(6645772957084084121176894227597/7812500000000000000), (65242909225850238071615466116307/39062500000000000000);
    (65242909225850238071615466116307/39062500000000000000), (135607501551047732273009539644201/39062500000000000000)]

private def f404desc11IntegerCoordinates : Matrix (Fin 54) (Fin 2) ℤ :=
  !![1, (-1);
    29, (-29);
    127, (-121);
    337, (-271);
    619, (-289);
    869, 121;
    1023, 957;
    1089, 1683;
    242, (-248);
    1782, (-1794);
    3864, (-3336);
    5698, (-2398);
    6556, 3344;
    6798, 11418;
    3432, 7656;
    2646, (-2772);
    8844, (-8712);
    10010, (-5390);
    10098, 5346;
    10824, 15312;
    5500, (-6820);
    11550, (-17490);
    16368, (-22704);
    10164, (-12936);
    10230, (-26070);
    36036, (-91476);
    8316, (-22176);
    550, (-604);
    4620, (-5352);
    6732, (-7128);
    5390, 220;
    2574, 17424;
    1320, 32736;
    7986, (-12012);
    3960, (-18480);
    (-20790), 22770;
    (-30096), 76032;
    (-13860), 49896;
    (-19140), (-660);
    (-55440), 7920;
    (-25872), (-7392);
    (-2310), (-53130);
    24948, (-94248);
    (-1650), (-4620);
    (-46530), 13860;
    (-69300), 55440;
    (-52668), 77616;
    (-97680), 50160;
    (-101640), 73920;
    5544, 11088;
    76230, (-62370);
    (-18480), 18480;
    138600, (-27720);
    103950, (-34650)]

private def f404desc11IntegerLeftProduct : Matrix (Fin 2) (Fin 54) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 2644429272917642277310358739993600, 0, 0, 0, 0, 0, 34696962924581561075326052352000, 877742012775481971446967537715200, 0, 0, 0, (-4766629062766065453996445900800), 112443144340156445642315094144000, 0, 615373503261060284766447206400, (-27025066279535372955820205107200), 0, 22340139958178998949989275033600, 0, 0, 0, 0, 0, 0, (-5896129824675244973006460518400), 98728501516177005256985841024000, 0, 0, 2148983806987974562802948505600, (-24977345461558582350191401036800), 0, (-2514935150188218127542935347200), 150013905007609349849907072000, 0, 0, 0, 0, 148175915447875669503580569600, 15912377546963840340807964262400, 0, (-8325469324184339864960207769600), 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 5291511522261393416285208361651200, 0, 0, 0, 0, 0, 68774286465770657628516762009600, 1768119435287517496975367015577600, 0, 0, 0, (-9448132399416868505207189299200), 244003497483412925838993835699200, 0, 1219757226136792351766360064000, (-57603451603756776234158351001600), 0, 48710849436060806306930223513600, 0, 0, 0, 0, 0, 0, (-11686962446232891063639153868800), 215326910665323190594021959705600, 0, 0, 4259589773570063946382137753600, (-51675299759981520886465957708800), 0, (-4984956891168601963609676390400), 2320628965185163377443848934400, 0, 0, 0, 0, 293705703080692189438065868800, 36925367627050153970108118220800, 0, (-15393004687600744307070649651200), 0, 0, 0, 0, 0, 0]

private def f404desc11IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![7655930446560864907595782150191744000, 15031966285635894851700203393197132800;
    15031966285635894851700203393197132800, 31243968357361397515701397934023910400]

private theorem f404desc11_coordinates_decode : natFourIntegerMatrix 3 f404desc11IntegerCoordinates=f404desc11 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc11IntegerCoordinates) (f404desc11) (by decide +kernel) a b

#print axioms f404desc11_coordinates_decode

private theorem f404desc11_left_row0_columns0 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 0=f404desc11IntegerLeftProduct 0 0) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 1=f404desc11IntegerLeftProduct 0 1) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 2=f404desc11IntegerLeftProduct 0 2) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 3=f404desc11IntegerLeftProduct 0 3) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 4=f404desc11IntegerLeftProduct 0 4) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 5=f404desc11IntegerLeftProduct 0 5) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 6=f404desc11IntegerLeftProduct 0 6) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 7=f404desc11IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f404desc11_left_row0_columns0

private theorem f404desc11_left_row0_columns1 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 8=f404desc11IntegerLeftProduct 0 8) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 9=f404desc11IntegerLeftProduct 0 9) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 10=f404desc11IntegerLeftProduct 0 10) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 11=f404desc11IntegerLeftProduct 0 11) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 12=f404desc11IntegerLeftProduct 0 12) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 13=f404desc11IntegerLeftProduct 0 13) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 14=f404desc11IntegerLeftProduct 0 14) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 15=f404desc11IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f404desc11_left_row0_columns1

private theorem f404desc11_left_row0_columns2 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 16=f404desc11IntegerLeftProduct 0 16) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 17=f404desc11IntegerLeftProduct 0 17) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 18=f404desc11IntegerLeftProduct 0 18) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 19=f404desc11IntegerLeftProduct 0 19) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 20=f404desc11IntegerLeftProduct 0 20) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 21=f404desc11IntegerLeftProduct 0 21) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 22=f404desc11IntegerLeftProduct 0 22) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 23=f404desc11IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f404desc11_left_row0_columns2

private theorem f404desc11_left_row0_columns3 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 24=f404desc11IntegerLeftProduct 0 24) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 25=f404desc11IntegerLeftProduct 0 25) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 26=f404desc11IntegerLeftProduct 0 26) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 27=f404desc11IntegerLeftProduct 0 27) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 28=f404desc11IntegerLeftProduct 0 28) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 29=f404desc11IntegerLeftProduct 0 29) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 30=f404desc11IntegerLeftProduct 0 30) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 31=f404desc11IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f404desc11_left_row0_columns3

private theorem f404desc11_left_row0_columns4 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 32=f404desc11IntegerLeftProduct 0 32) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 33=f404desc11IntegerLeftProduct 0 33) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 34=f404desc11IntegerLeftProduct 0 34) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 35=f404desc11IntegerLeftProduct 0 35) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 36=f404desc11IntegerLeftProduct 0 36) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 37=f404desc11IntegerLeftProduct 0 37) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 38=f404desc11IntegerLeftProduct 0 38) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 39=f404desc11IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f404desc11_left_row0_columns4

private theorem f404desc11_left_row0_columns5 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 40=f404desc11IntegerLeftProduct 0 40) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 41=f404desc11IntegerLeftProduct 0 41) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 42=f404desc11IntegerLeftProduct 0 42) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 43=f404desc11IntegerLeftProduct 0 43) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 44=f404desc11IntegerLeftProduct 0 44) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 45=f404desc11IntegerLeftProduct 0 45) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 46=f404desc11IntegerLeftProduct 0 46) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 47=f404desc11IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f404desc11_left_row0_columns5

private theorem f404desc11_left_row0_columns6 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 48=f404desc11IntegerLeftProduct 0 48) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 49=f404desc11IntegerLeftProduct 0 49) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 50=f404desc11IntegerLeftProduct 0 50) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 51=f404desc11IntegerLeftProduct 0 51) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 52=f404desc11IntegerLeftProduct 0 52) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 0 53=f404desc11IntegerLeftProduct 0 53) := by
  decide +kernel

#print axioms f404desc11_left_row0_columns6

private theorem f404desc11_left_row1_columns0 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 0=f404desc11IntegerLeftProduct 1 0) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 1=f404desc11IntegerLeftProduct 1 1) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 2=f404desc11IntegerLeftProduct 1 2) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 3=f404desc11IntegerLeftProduct 1 3) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 4=f404desc11IntegerLeftProduct 1 4) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 5=f404desc11IntegerLeftProduct 1 5) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 6=f404desc11IntegerLeftProduct 1 6) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 7=f404desc11IntegerLeftProduct 1 7) := by
  decide +kernel

#print axioms f404desc11_left_row1_columns0

private theorem f404desc11_left_row1_columns1 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 8=f404desc11IntegerLeftProduct 1 8) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 9=f404desc11IntegerLeftProduct 1 9) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 10=f404desc11IntegerLeftProduct 1 10) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 11=f404desc11IntegerLeftProduct 1 11) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 12=f404desc11IntegerLeftProduct 1 12) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 13=f404desc11IntegerLeftProduct 1 13) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 14=f404desc11IntegerLeftProduct 1 14) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 15=f404desc11IntegerLeftProduct 1 15) := by
  decide +kernel

#print axioms f404desc11_left_row1_columns1

private theorem f404desc11_left_row1_columns2 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 16=f404desc11IntegerLeftProduct 1 16) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 17=f404desc11IntegerLeftProduct 1 17) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 18=f404desc11IntegerLeftProduct 1 18) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 19=f404desc11IntegerLeftProduct 1 19) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 20=f404desc11IntegerLeftProduct 1 20) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 21=f404desc11IntegerLeftProduct 1 21) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 22=f404desc11IntegerLeftProduct 1 22) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 23=f404desc11IntegerLeftProduct 1 23) := by
  decide +kernel

#print axioms f404desc11_left_row1_columns2

private theorem f404desc11_left_row1_columns3 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 24=f404desc11IntegerLeftProduct 1 24) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 25=f404desc11IntegerLeftProduct 1 25) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 26=f404desc11IntegerLeftProduct 1 26) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 27=f404desc11IntegerLeftProduct 1 27) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 28=f404desc11IntegerLeftProduct 1 28) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 29=f404desc11IntegerLeftProduct 1 29) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 30=f404desc11IntegerLeftProduct 1 30) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 31=f404desc11IntegerLeftProduct 1 31) := by
  decide +kernel

#print axioms f404desc11_left_row1_columns3

private theorem f404desc11_left_row1_columns4 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 32=f404desc11IntegerLeftProduct 1 32) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 33=f404desc11IntegerLeftProduct 1 33) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 34=f404desc11IntegerLeftProduct 1 34) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 35=f404desc11IntegerLeftProduct 1 35) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 36=f404desc11IntegerLeftProduct 1 36) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 37=f404desc11IntegerLeftProduct 1 37) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 38=f404desc11IntegerLeftProduct 1 38) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 39=f404desc11IntegerLeftProduct 1 39) := by
  decide +kernel

#print axioms f404desc11_left_row1_columns4

private theorem f404desc11_left_row1_columns5 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 40=f404desc11IntegerLeftProduct 1 40) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 41=f404desc11IntegerLeftProduct 1 41) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 42=f404desc11IntegerLeftProduct 1 42) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 43=f404desc11IntegerLeftProduct 1 43) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 44=f404desc11IntegerLeftProduct 1 44) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 45=f404desc11IntegerLeftProduct 1 45) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 46=f404desc11IntegerLeftProduct 1 46) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 47=f404desc11IntegerLeftProduct 1 47) := by
  decide +kernel

#print axioms f404desc11_left_row1_columns5

private theorem f404desc11_left_row1_columns6 :
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 48=f404desc11IntegerLeftProduct 1 48) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 49=f404desc11IntegerLeftProduct 1 49) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 50=f404desc11IntegerLeftProduct 1 50) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 51=f404desc11IntegerLeftProduct 1 51) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 52=f404desc11IntegerLeftProduct 1 52) ∧
    ((f404desc11IntegerCoordinatesᵀ*f415rawInteger) 1 53=f404desc11IntegerLeftProduct 1 53) := by
  decide +kernel

#print axioms f404desc11_left_row1_columns6

theorem f404desc11_compression_check :
    f404desc11ᵀ*f415rawM4Form*f404desc11=f404desc11Form := by
  have hD := f404desc11_coordinates_decode
  have hV : f404desc11IntegerCoordinatesᵀ*f415rawInteger=f404desc11IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f404desc11_left_row0_columns0.1
      · exact f404desc11_left_row0_columns0.2.1
      · exact f404desc11_left_row0_columns0.2.2.1
      · exact f404desc11_left_row0_columns0.2.2.2.1
      · exact f404desc11_left_row0_columns0.2.2.2.2.1
      · exact f404desc11_left_row0_columns0.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns0.2.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns0.2.2.2.2.2.2.2
      · exact f404desc11_left_row0_columns1.1
      · exact f404desc11_left_row0_columns1.2.1
      · exact f404desc11_left_row0_columns1.2.2.1
      · exact f404desc11_left_row0_columns1.2.2.2.1
      · exact f404desc11_left_row0_columns1.2.2.2.2.1
      · exact f404desc11_left_row0_columns1.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns1.2.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns1.2.2.2.2.2.2.2
      · exact f404desc11_left_row0_columns2.1
      · exact f404desc11_left_row0_columns2.2.1
      · exact f404desc11_left_row0_columns2.2.2.1
      · exact f404desc11_left_row0_columns2.2.2.2.1
      · exact f404desc11_left_row0_columns2.2.2.2.2.1
      · exact f404desc11_left_row0_columns2.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns2.2.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns2.2.2.2.2.2.2.2
      · exact f404desc11_left_row0_columns3.1
      · exact f404desc11_left_row0_columns3.2.1
      · exact f404desc11_left_row0_columns3.2.2.1
      · exact f404desc11_left_row0_columns3.2.2.2.1
      · exact f404desc11_left_row0_columns3.2.2.2.2.1
      · exact f404desc11_left_row0_columns3.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns3.2.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns3.2.2.2.2.2.2.2
      · exact f404desc11_left_row0_columns4.1
      · exact f404desc11_left_row0_columns4.2.1
      · exact f404desc11_left_row0_columns4.2.2.1
      · exact f404desc11_left_row0_columns4.2.2.2.1
      · exact f404desc11_left_row0_columns4.2.2.2.2.1
      · exact f404desc11_left_row0_columns4.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns4.2.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns4.2.2.2.2.2.2.2
      · exact f404desc11_left_row0_columns5.1
      · exact f404desc11_left_row0_columns5.2.1
      · exact f404desc11_left_row0_columns5.2.2.1
      · exact f404desc11_left_row0_columns5.2.2.2.1
      · exact f404desc11_left_row0_columns5.2.2.2.2.1
      · exact f404desc11_left_row0_columns5.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns5.2.2.2.2.2.2.1
      · exact f404desc11_left_row0_columns5.2.2.2.2.2.2.2
      · exact f404desc11_left_row0_columns6.1
      · exact f404desc11_left_row0_columns6.2.1
      · exact f404desc11_left_row0_columns6.2.2.1
      · exact f404desc11_left_row0_columns6.2.2.2.1
      · exact f404desc11_left_row0_columns6.2.2.2.2.1
      · exact f404desc11_left_row0_columns6.2.2.2.2.2
    · fin_cases b
      · exact f404desc11_left_row1_columns0.1
      · exact f404desc11_left_row1_columns0.2.1
      · exact f404desc11_left_row1_columns0.2.2.1
      · exact f404desc11_left_row1_columns0.2.2.2.1
      · exact f404desc11_left_row1_columns0.2.2.2.2.1
      · exact f404desc11_left_row1_columns0.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns0.2.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns0.2.2.2.2.2.2.2
      · exact f404desc11_left_row1_columns1.1
      · exact f404desc11_left_row1_columns1.2.1
      · exact f404desc11_left_row1_columns1.2.2.1
      · exact f404desc11_left_row1_columns1.2.2.2.1
      · exact f404desc11_left_row1_columns1.2.2.2.2.1
      · exact f404desc11_left_row1_columns1.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns1.2.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns1.2.2.2.2.2.2.2
      · exact f404desc11_left_row1_columns2.1
      · exact f404desc11_left_row1_columns2.2.1
      · exact f404desc11_left_row1_columns2.2.2.1
      · exact f404desc11_left_row1_columns2.2.2.2.1
      · exact f404desc11_left_row1_columns2.2.2.2.2.1
      · exact f404desc11_left_row1_columns2.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns2.2.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns2.2.2.2.2.2.2.2
      · exact f404desc11_left_row1_columns3.1
      · exact f404desc11_left_row1_columns3.2.1
      · exact f404desc11_left_row1_columns3.2.2.1
      · exact f404desc11_left_row1_columns3.2.2.2.1
      · exact f404desc11_left_row1_columns3.2.2.2.2.1
      · exact f404desc11_left_row1_columns3.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns3.2.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns3.2.2.2.2.2.2.2
      · exact f404desc11_left_row1_columns4.1
      · exact f404desc11_left_row1_columns4.2.1
      · exact f404desc11_left_row1_columns4.2.2.1
      · exact f404desc11_left_row1_columns4.2.2.2.1
      · exact f404desc11_left_row1_columns4.2.2.2.2.1
      · exact f404desc11_left_row1_columns4.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns4.2.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns4.2.2.2.2.2.2.2
      · exact f404desc11_left_row1_columns5.1
      · exact f404desc11_left_row1_columns5.2.1
      · exact f404desc11_left_row1_columns5.2.2.1
      · exact f404desc11_left_row1_columns5.2.2.2.1
      · exact f404desc11_left_row1_columns5.2.2.2.2.1
      · exact f404desc11_left_row1_columns5.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns5.2.2.2.2.2.2.1
      · exact f404desc11_left_row1_columns5.2.2.2.2.2.2.2
      · exact f404desc11_left_row1_columns6.1
      · exact f404desc11_left_row1_columns6.2.1
      · exact f404desc11_left_row1_columns6.2.2.1
      · exact f404desc11_left_row1_columns6.2.2.2.1
      · exact f404desc11_left_row1_columns6.2.2.2.2.1
      · exact f404desc11_left_row1_columns6.2.2.2.2.2
  have hY : f404desc11IntegerLeftProduct*f404desc11IntegerCoordinates=f404desc11IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc11IntegerLeftProduct*f404desc11IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc11IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc11IntegerLeftProduct*f404desc11IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc11IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc11IntegerForm=f404desc11Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc11IntegerForm) (f404desc11Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f415rawInteger f404desc11IntegerCoordinates f404desc11IntegerLeftProduct f404desc11IntegerForm
    f415rawM4Form f404desc11 f404desc11Form f415_raw_integer_check hD hV hY hF

theorem f404desc11_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc11Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 11
    f404basis b404relative
    f415basis f404desc11 f415rawM4Form f404desc11Form
    f404desc11_actual f415_actual_raw_M4_matrix f404desc11_compression_check x y


#print axioms f404desc11_compression_check
#print axioms f404desc11_source_form
end TorusLean.BosonFiniteCertificate
