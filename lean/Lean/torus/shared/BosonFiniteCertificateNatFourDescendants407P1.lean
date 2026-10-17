import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
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

def f407desc1Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(79658266151025878914818201/1562500000000000000000000), (-100695345724106224507474633/1562500000000000000000000);
    (-100695345724106224507474633/1562500000000000000000000), (18363410231431888683592933/195312500000000000000000)]

private def f407desc1IntegerCoordinates : Matrix (Fin 15) (Fin 2) ℤ :=
  !![3, (-4);
    (-12), 16;
    6, 12;
    12, (-16);
    (-15), 0;
    (-6), (-12);
    36, (-88);
    0, 80;
    (-90), 60;
    60, (-40);
    36, (-8);
    (-90), 140;
    60, (-120);
    0, (-80);
    0, 60]

private def f407desc1IntegerLeftProduct : Matrix (Fin 2) (Fin 15) ℤ :=
  !![10937414595520114882541280000, 412266194328519516299178240, 3551005507698674235873882432, (-3539982093594339699838065888), (-3242906223520705120656322560), 50186403768145464556531200, 341327785363984499004367488, (-1283512646928543541894369440), 577742273493622239364579584, 980638427178321726938059584, 257714669377197788426291520, (-631029097642020507985358592), 721653745489102189805964480, 614966749618173855397701984, 1166370299611398402740222976;
    (-9494703665358830794825747200), 2754895233311260982615030400, (-5676545909059918506035229696), 1818919101418358031528190464, 2452203078527817776749885440, 943194925483294140645434880, 112648989701488759228358016, 1655261223487510294835077440, (-485038149418964367659761152), (-1032892119897141763971388032), 838063271445042965963477760, 1353320524761104063567840256, (-164857686850448909554427520), (-1250582510257944095546841792), (-1205903975419198160943141888)]

private def f407desc1IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![183532645211963625019741135104, (-232002076548340741265221554432);
    (-232002076548340741265221554432), 338474377385752572215984941056]

theorem f407desc1_compression_check :
    f407desc1ᵀ*f408rawM4Form*f407desc1=f407desc1Form := by
  have hD : natFourIntegerMatrix 60 f407desc1IntegerCoordinates=f407desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc1IntegerCoordinates) (f407desc1) (by decide +kernel) a b
  have hV : f407desc1IntegerCoordinatesᵀ*f408rawInteger=f407desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f407desc1IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f407desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f407desc1IntegerCoordinatesᵀ*f408rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f407desc1IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407desc1IntegerLeftProduct*f407desc1IntegerCoordinates=f407desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc1IntegerLeftProduct*f407desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc1IntegerLeftProduct*f407desc1IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc1IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc1IntegerForm=f407desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc1IntegerForm) (f407desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f408rawInteger f407desc1IntegerCoordinates f407desc1IntegerLeftProduct f407desc1IntegerForm
    f408rawM4Form f407desc1 f407desc1Form f408_raw_integer_check hD hV hY hF

theorem f407desc1_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f407basis b407relative
    f408basis f407desc1 f408rawM4Form f407desc1Form
    f407desc1_actual f408_actual_raw_M4_matrix f407desc1_compression_check x y


#print axioms f407desc1_compression_check
#print axioms f407desc1_source_form
end TorusLean.BosonFiniteCertificate
