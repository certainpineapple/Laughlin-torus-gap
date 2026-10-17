import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
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
import torus.shared.BosonFiniteCertificate406

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

def f406desc5Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(9592795663856333630304349149/7812500000000000000000), (-3123644041150569785256667317/7812500000000000000000), (-3391987566218165310201437451/15625000000000000000000);
    (-3123644041150569785256667317/7812500000000000000000), (4328860257255731576001780123/3906250000000000000000), (13380137294534524886917075083/15625000000000000000000);
    (-3391987566218165310201437451/15625000000000000000000), (13380137294534524886917075083/15625000000000000000000), (3391188034696601293733845713/3906250000000000000000)]

private def f406desc5IntegerCoordinates : Matrix (Fin 27) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    (-27), 27, 27;
    (-45), 15, 5;
    (-75), (-15), (-65);
    (-60), 30, (-80);
    24, 126, (-24);
    0, 30, 40;
    90, (-150), (-110);
    (-120), (-240), (-200);
    60, 0, 120;
    216, 84, 184;
    (-90), (-120), (-10);
    (-780), 120, 460;
    0, 240, 620;
    (-180), 240, 140;
    450, 150, (-250);
    180, (-30), (-20);
    720, (-120), (-160);
    120, (-120), (-40);
    540, (-660), (-100);
    (-270), 720, 330;
    (-1440), 480, (-80);
    450, (-1050), (-950);
    900, (-1200), (-1900);
    (-810), 840, 510;
    (-450), 600, 950;
    600, 0, 600]

private def f406desc5IntegerLeftProduct : Matrix (Fin 3) (Fin 27) ℤ :=
  !![0, 0, 0, (-55815640052300537953278009600), (-216723600584866207738433243520), 1479758786541909957236885798400, 0, 6843867644329142824928563200, (-189393913728408529593037635840), 536006328531857344293290991360, 754688093630528695563063619200, (-42182497446827715744162883200), (-51407587128376280855117537280), 178366094504304029898472946880, (-120993919341185754845093612160), 243827640660318615381258138240, 3980067465647821510619596800, 17499892221089077552979788800, 20288017527744669810569930880, 80231786186487558134489121600, (-146641377788644161116557296000), (-207931665715305818936598627840), 238728123998717669683499612160, 44152449251864915980831622400, (-181403309211463091062453651200), 35558378414990097175325704320, (-29527922901380721963064807680);
    0, 0, 0, 162760112259372029988499852800, 783326253937213484198692444800, 2254199244296333817854518905600, 0, 18910198966479104240122521600, 139203549369693867972789757440, 354742674735685311098223863040, 1148955386109850690041041942400, (-72212383749032066189433974400), 15243587355191379368565300480, 236992334932661678287648130880, 160513418668761423758422776960, (-155352596134888358515909163520), 10997271616517558866645401600, 489863323388620251682617600, (-32391961574180016375407882880), 57935672980337522543397560640, (-10684770440736805997458780800), 136851390815811515349321421440, (-278259228101027230875002557440), (-73736381103268614261392044800), 183934959155935967563526966400, (-14993001716350572391796179200), (-11219837266528424987128341120);
    0, 0, 0, (-44392419939577774170411993600), (-1066229801365284139168189837440), 1216916202549552618087373363200, 0, 21117184689928192685232537600, 9891947775806309278029565440, 90147084932844442609361245440, 1172552284621074014519780131200, 3445878112381284559757366400, 26717643126313447093999994880, 218642336679856611575209723200, 212317878640034943815571538560, (-49058408990028398858380759680), 12280749513489576189558835200, 9160044697040194630341849600, (-34379084204503908142688830080), 24111141459316118088867126720, 943709304296177004689366400, 138248783396215992745200771840, (-204909335550643364097963264000), (-35516078639447159201573433600), 177177014140062846569393548800, (-5862931129005574517734124160), (-38594067338147455499483877120)]

private def f406desc5IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1105090060476249634211061021964800, (-359843793540545639261568074918400), (-195378483814166321867602797177600);
    (-359843793540545639261568074918400), 997369403271720555110810140339200, 770695908165188633486423524780800;
    (-195378483814166321867602797177600), 770695908165188633486423524780800, 781329723194096938076278052275200]

theorem f406desc5_compression_check :
    f406desc5ᵀ*f411rawM4Form*f406desc5=f406desc5Form := by
  have hD : natFourIntegerMatrix 30 f406desc5IntegerCoordinates=f406desc5 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc5IntegerCoordinates) (f406desc5) (by decide +kernel) a b
  have hV : f406desc5IntegerCoordinatesᵀ*f411rawInteger=f406desc5IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f406desc5IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f406desc5IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f406desc5IntegerCoordinatesᵀ*f411rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f406desc5IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f406desc5IntegerCoordinatesᵀ*f411rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f406desc5IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc5IntegerLeftProduct*f406desc5IntegerCoordinates=f406desc5IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc5IntegerLeftProduct*f406desc5IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc5IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc5IntegerLeftProduct*f406desc5IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc5IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc5IntegerLeftProduct*f406desc5IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc5IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc5IntegerForm=f406desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc5IntegerForm) (f406desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f411rawInteger f406desc5IntegerCoordinates f406desc5IntegerLeftProduct f406desc5IntegerForm
    f411rawM4Form f406desc5 f406desc5Form f411_raw_integer_check hD hV hY hF

theorem f406desc5_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f406basis b406relative
    f411basis f406desc5 f411rawM4Form f406desc5Form
    f406desc5_actual f411_actual_raw_M4_matrix f406desc5_compression_check x y


#print axioms f406desc5_compression_check
#print axioms f406desc5_source_form
end TorusLean.BosonFiniteCertificate
