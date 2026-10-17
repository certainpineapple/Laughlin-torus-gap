import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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

def f407desc3Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(33032873030751416377896651/15625000000000000000000), (-575510588453200687676610909/156250000000000000000000);
    (-575510588453200687676610909/156250000000000000000000), (59071195900088921918013943/19531250000000000000000)]

private def f407desc3IntegerCoordinates : Matrix (Fin 23) (Fin 2) ℤ :=
  !![3, (-4);
    6, (-8);
    (-9), 32;
    12, 24;
    0, (-20);
    (-18), (-16);
    (-36), 28;
    (-36), 8;
    132, (-136);
    (-36), 88;
    (-18), (-116);
    (-108), 24;
    (-90), 200;
    120, 0;
    0, 0;
    180, (-120);
    144, (-32);
    0, 60;
    (-216), 288;
    (-180), (-280);
    240, (-480);
    (-270), 420;
    180, 40]

private def f407desc3IntegerLeftProduct : Matrix (Fin 2) (Fin 23) ℤ :=
  !![0, 0, (-12596212965514299857815518720), (-43938092017796243849197407360), (-96829350312834486640152984960), (-137662196666042913433836192000), (-815358684339741133180108800), (-355415426298189295498016640), (-21878961651769153426630442496), (-71927974875232296706928561856), 3749428138680725148948476160, (-39897718931183816411287509312), (-31281870341878420595702563584), (-20062712532727112915967141888), (-3388715700622428640817364480), (-2602244156635698225566215680), (-40960399825961519997926413440), (-14303847045010445418895105536), (-28988887831187337693101134080), (-10445318062980555882196963584), (-7949515514759488971970419456), (-9073068597540187314223834368), (-6461074967136538281349549824);
    0, 0, 66529709126368881897082344960, 42538690935725876451928373760, 89206770139287652830603778560, 173274474964644571797499161600, 806608840760901976702464000, (-17887960812379655559751534080), 1558373415295518848571717888, 65927007823686331205571065088, 18261535252496815733372305920, 68009717790762067731842105856, 20139396176535511244642936832, 37615020652673841161126928384, (-2285409095433008917288680960), (-1234519967996424306845928960), 66596044849538396455302677760, 20068711745024175945243706368, 55451901259053314672120394240, 22698599991880976078957048832, 17440299506534381728032757248, 6344617716209476311344031744, 3865750243826106575844774912]

private def f407desc3IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![7610773946285126333467388390400, (-13259763957961743844069115343360);
    (-13259763957961743844069115343360), 10888002828304390087928329973760]

theorem f407desc3_compression_check :
    f407desc3ᵀ*f410rawM4Form*f407desc3=f407desc3Form := by
  have hD : natFourIntegerMatrix 60 f407desc3IntegerCoordinates=f407desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc3IntegerCoordinates) (f407desc3) (by decide +kernel) a b
  have hV : f407desc3IntegerCoordinatesᵀ*f410rawInteger=f407desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f407desc3IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f407desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f407desc3IntegerCoordinatesᵀ*f410rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f407desc3IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407desc3IntegerLeftProduct*f407desc3IntegerCoordinates=f407desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc3IntegerLeftProduct*f407desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc3IntegerLeftProduct*f407desc3IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc3IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc3IntegerForm=f407desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc3IntegerForm) (f407desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f410rawInteger f407desc3IntegerCoordinates f407desc3IntegerLeftProduct f407desc3IntegerForm
    f410rawM4Form f407desc3 f407desc3Form f410_raw_integer_check hD hV hY hF

theorem f407desc3_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f407basis b407relative
    f410basis f407desc3 f410rawM4Form f407desc3Form
    f407desc3_actual f410_actual_raw_M4_matrix f407desc3_compression_check x y


#print axioms f407desc3_compression_check
#print axioms f407desc3_source_form
end TorusLean.BosonFiniteCertificate
