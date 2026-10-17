import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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
import torus.shared.BosonFiniteCertificate405

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

def f405desc5Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(2236643635217528959645401277/4687500000000000000000)]

private def f405desc5IntegerCoordinates : Matrix (Fin 23) (Fin 1) ℤ :=
  !![(-1);
    (-10);
    (-7);
    8;
    10;
    2;
    (-18);
    32;
    64;
    (-40);
    76;
    96;
    (-10);
    40;
    0;
    40;
    (-128);
    (-150);
    (-24);
    (-320);
    0;
    60;
    280]

private def f405desc5IntegerLeftProduct : Matrix (Fin 1) (Fin 23) ℤ :=
  !![0, 0, (-11031035903399067876007384320), (-52267573473806084651647102080), (-36186843694685403526895396736), (-53736630444599030760599758080), 122277208109120026215966720, 12893510492424359051563720320, (-11564891684711141715629665920), (-64796102520671121512825617344), 17056089399134712243463872000, (-36363910303271939289047793600), (-39544626399606891849946631424), (-34676599651394031806924795904), 3242977226407459516183891200, 4352264510057396764548445440, (-41809087175412308300251276800), (-43515374772685366091573535744), (-18282297281504056592888524800), (-24079317718063609095618901248), (-14536248260168193332730485760), (-7717057671106642500923588352), (-2936418601542810648007668480)]

private def f405desc5IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![17177423118470622410076681807360]

theorem f405desc5_compression_check :
    f405desc5ᵀ*f410rawM4Form*f405desc5=f405desc5Form := by
  have hD : natFourIntegerMatrix 6 f405desc5IntegerCoordinates=f405desc5 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc5IntegerCoordinates) (f405desc5) (by decide +kernel) a b
  have hV : f405desc5IntegerCoordinatesᵀ*f410rawInteger=f405desc5IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f405desc5IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f405desc5IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc5IntegerLeftProduct*f405desc5IntegerCoordinates=f405desc5IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc5IntegerLeftProduct*f405desc5IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc5IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc5IntegerForm=f405desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc5IntegerForm) (f405desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f410rawInteger f405desc5IntegerCoordinates f405desc5IntegerLeftProduct f405desc5IntegerForm
    f410rawM4Form f405desc5 f405desc5Form f410_raw_integer_check hD hV hY hF

theorem f405desc5_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f405basis b405relative
    f410basis f405desc5 f410rawM4Form f405desc5Form
    f405desc5_actual f410_actual_raw_M4_matrix f405desc5_compression_check x y


#print axioms f405desc5_compression_check
#print axioms f405desc5_source_form
end TorusLean.BosonFiniteCertificate
