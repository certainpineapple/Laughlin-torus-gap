import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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

def f404desc12Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(166206069202040435836207863/610351562500000), (74757344271705621612071161407/152587890625000000);
    (74757344271705621612071161407/152587890625000000), (134499553461306508541645784051/152587890625000000)]

private def f404desc12IntegerCoordinates : Matrix (Fin 64) (Fin 2) ℤ :=
  !![1, (-1);
    32, (-32);
    156, (-150);
    464, (-392);
    956, (-560);
    1488, (-168);
    1892, 1078;
    2112, 2640;
    1089, 1683;
    300, (-306);
    2520, (-2532);
    6320, (-5672);
    10800, (-6312);
    13992, 1188;
    15400, 16676;
    15840, 30096;
    4428, (-4566);
    18000, (-17592);
    24552, (-16500);
    26664, 3300;
    27720, 32076;
    14256, 22968;
    14344, (-15532);
    32560, (-36520);
    38016, (-34848);
    47520, (-33264);
    21780, (-43560);
    72864, (-166320);
    46200, (-104412);
    60984, (-158004);
    792, (-852);
    8052, (-8958);
    15216, (-15816);
    17820, (-9306);
    14520, 20988;
    10692, 61578;
    4752, 40392;
    19872, (-25488);
    42240, (-65472);
    3960, (-660);
    (-35640), 138996;
    (-44352), 256608;
    (-9680), (-25960);
    (-102960), 11880;
    (-95040), 53856;
    (-29568), 29568;
    (-47520), (-71280);
    55440, (-393624);
    33264, (-116424);
    6336, (-16632);
    (-47520), (-18480);
    (-136620), 92070;
    (-152064), 209088;
    (-66528), 127512;
    (-209880), 77220;
    (-491040), 293040;
    (-221760), 243936;
    (-27720), (-41580);
    182952, (-207900);
    (-116160), 68640;
    (-18480), 101640;
    144144, (-16632);
    665280, (-221760);
    103950, (-34650)]

private def f404desc12IntegerLeftProduct : Matrix (Fin 2) (Fin 64) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, (-2049792734858182764548810342400), 0, 0, 0, 0, 0, 0, 219840263536237499825150164992000, 0, 0, 0, 0, (-32577062013187379099524133683200), 0, 0, 0, 7833136195398409544784199680000, 0, (-5344102298297401063718849740800), 0, 0, 0, 0, 0, 0, 0, 0, (-30380855646689674951606006579200), 0, 0, 0, 0, 7101067422031136121463573708800, 0, 0, (-805275677816353428998455296000), 0, 0, 0, 0, 0, 0, 0, (-3733550817681331000237208371200), 0, 0, 1537344576166990057803812044800, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, (-3687881240465695562727378124800), 0, 0, 0, 0, 0, 0, 395525249946993687008653541376000, 0, 0, 0, 0, (-58610967745591026146176833945600), 0, 0, 0, 14092974151857795712711960166400, 0, (-9614832894011549487368326348800), 0, 0, 0, 0, 0, 0, 0, 0, (-54659666659650510085899367219200), 0, 0, 0, 0, 12775873817702010280982917939200, 0, 0, (-1448810416350502492352318668800), 0, 0, 0, 0, 0, 0, 0, (-6717211836446803984358827622400), 0, 0, 2765910975370028442386222284800, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f404desc12IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2450808214025607450666386664652800000, 4409367582771449656171826070572236800;
    4409367582771449656171826070572236800, 7933106462076165009406768293209702400]

def f404desc12IntegerCoordinatesShared := f404desc12IntegerCoordinates

def f404desc12IntegerLeftProductShared := f404desc12IntegerLeftProduct

def f404desc12IntegerFormShared := f404desc12IntegerForm


end TorusLean.BosonFiniteCertificate
