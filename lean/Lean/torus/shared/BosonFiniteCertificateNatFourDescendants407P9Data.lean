import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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

def f407desc9Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1455258855487391770051787103/61035156250000000000), (745628574612319975044164529/15258789062500000000);
    (745628574612319975044164529/15258789062500000000), (1528145921756867066531369163/15258789062500000000)]

private def f407desc9IntegerCoordinates : Matrix (Fin 64) (Fin 2) ℤ :=
  !![3, (-4);
    60, (-80);
    162, (-196);
    228, (-144);
    192, 264;
    108, 656;
    (-66), 388;
    (-396), (-432);
    (-297), (-444);
    306, (-428);
    1044, (-1432);
    480, 240;
    (-144), 3632;
    396, 3992;
    (-132), (-424);
    (-2376), (-4992);
    (-54), (-308);
    (-3672), 3536;
    (-3924), 4712;
    (-1620), 280;
    (-5508), (-1656);
    (-4968), (-336);
    (-4188), 1224;
    (-5520), (-7440);
    (-5400), (-4800);
    (-14832), 14496;
    (-1080), (-6360);
    (-4320), 19680;
    (-4284), 23352;
    756, 31752;
    324, (-552);
    54, (-1092);
    (-1944), 3312;
    1458, 5076;
    8244, (-392);
    7398, (-5604);
    1944, (-3312);
    (-5184), 3312;
    (-11232), 10656;
    19620, (-11800);
    33372, (-19656);
    4320, 9600;
    5640, (-14160);
    47520, (-77040);
    23328, (-39744);
    (-6048), 4704;
    29160, (-57600);
    46872, (-94416);
    13608, (-23184);
    (-4536), 3408;
    0, (-80);
    18630, (-7020);
    (-15552), 42336;
    (-25704), 42672;
    10260, (-8280);
    (-32400), 44640;
    (-139104), 158592;
    (-26460), (-840);
    (-6804), (-43848);
    (-12960), 22080;
    (-52920), 82320;
    (-13608), 23184;
    113400, (-100800);
    28350, (-25200)]

private def f407desc9IntegerLeftProduct : Matrix (Fin 2) (Fin 64) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 383607095204944448985976012800, 0, 0, 0, 0, 0, 0, (-41141859598824335491690561536000), 0, 0, 0, 0, 6096612558271532737659332198400, 0, 0, 0, (-1465927052604850547907084288000), 0, 1000118462840472518670739046400, 0, 0, 0, 0, 0, 0, 0, 0, 5685604981556185458724641177600, 0, 0, 0, 0, (-1328924529927309488962889318400), 0, 0, 150702780019218770722524364800, 0, 0, 0, 0, 0, 0, 0, 698712879412107108601410355200, 0, 0, (-287705326086687698290999296000), 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 786192533459747429965273497600, 0, 0, 0, 0, 0, 0, (-84319146422366709187020718080000), 0, 0, 0, 0, 12494845201309924661427850444800, 0, 0, 0, (-3004378484550299126293266432000), 0, 2049716175453766823154175180800, 0, 0, 0, 0, 0, 0, 0, 0, 11652496110148422932997518131200, 0, 0, 0, 0, (-2723595460094809913891114188800), 0, 0, 308861337299903437139745177600, 0, 0, 0, 0, 0, 0, 0, 1431993452916894377972229734400, 0, 0, (-589644409692458220444352512000), 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f407desc9IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![85834659917899536337902527623987200, 175915851356854806784179719661158400;
    175915851356854806784179719661158400, 360534856061728944259919314078924800]

def f407desc9IntegerCoordinatesShared := f407desc9IntegerCoordinates

def f407desc9IntegerLeftProductShared := f407desc9IntegerLeftProduct

def f407desc9IntegerFormShared := f407desc9IntegerForm


end TorusLean.BosonFiniteCertificate
