import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
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

def f405desc3Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1707361310095459670950531/5859375000000000000000)]

private def f405desc3IntegerCoordinates : Matrix (Fin 15) (Fin 1) ℤ :=
  !![(-1);
    (-4);
    4;
    4;
    (-1);
    4;
    24;
    (-24);
    12;
    8;
    0;
    (-36);
    (-32);
    24;
    18]

private def f405desc3IntegerLeftProduct : Matrix (Fin 1) (Fin 15) ℤ :=
  !![2485594443810935206893882240, 2128514066292090371788567488, 418856096354874675348473280, (-873421593483792606744105888), 2731169291600825032621953024, 1391757641789076351240552960, 109126881568460426643158592, (-513927287217077172986893824), (-1043755947895468649737351680), (-446331152754236351874460416), 139145258303654122084175424, (-946509938272509280759010304), (-97616969215243714711817088), (-506413110623257364994394368), (-190538126702630651772440064)]

private def f405desc3IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![10490027889226504218320062464]

theorem f405desc3_compression_check :
    f405desc3ᵀ*f408rawM4Form*f405desc3=f405desc3Form := by
  have hD : natFourIntegerMatrix 6 f405desc3IntegerCoordinates=f405desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc3IntegerCoordinates) (f405desc3) (by decide +kernel) a b
  have hV : f405desc3IntegerCoordinatesᵀ*f408rawInteger=f405desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f405desc3IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f405desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc3IntegerLeftProduct*f405desc3IntegerCoordinates=f405desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc3IntegerLeftProduct*f405desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc3IntegerForm=f405desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc3IntegerForm) (f405desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f408rawInteger f405desc3IntegerCoordinates f405desc3IntegerLeftProduct f405desc3IntegerForm
    f408rawM4Form f405desc3 f405desc3Form f408_raw_integer_check hD hV hY hF

theorem f405desc3_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f405basis b405relative
    f408basis f405desc3 f408rawM4Form f405desc3Form
    f405desc3_actual f408_actual_raw_M4_matrix f405desc3_compression_check x y


#print axioms f405desc3_compression_check
#print axioms f405desc3_source_form
end TorusLean.BosonFiniteCertificate
