import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger406
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

def f405desc1Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-4069516700435497421884279/1125000000000000000000000)]

private def f405desc1IntegerCoordinates : Matrix (Fin 9) (Fin 1) ℤ :=
  !![(-1);
    2;
    3;
    (-2);
    2;
    (-8);
    6;
    (-8);
    6]

private def f405desc1IntegerLeftProduct : Matrix (Fin 1) (Fin 9) ℤ :=
  !![594728524706560149663037728, 64721803831005374600001560, 27209465821866478600362032, 29065832567021156734349136, 10586641990296929509586080, 10056366990279210003346576, 4183815110376145136378544, (-44665497823225659120658320), (-1930928501227660357597920)]

private def f405desc1IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![(-130224534413935917500296928)]

theorem f405desc1_compression_check :
    f405desc1ᵀ*f406rawM4Form*f405desc1=f405desc1Form := by
  have hD : natFourIntegerMatrix 6 f405desc1IntegerCoordinates=f405desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc1IntegerCoordinates) (f405desc1) (by decide +kernel) a b
  have hV : f405desc1IntegerCoordinatesᵀ*f406rawInteger=f405desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f405desc1IntegerCoordinatesᵀ*f406rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f405desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc1IntegerLeftProduct*f405desc1IntegerCoordinates=f405desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc1IntegerLeftProduct*f405desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc1IntegerForm=f405desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc1IntegerForm) (f405desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f406rawInteger f405desc1IntegerCoordinates f405desc1IntegerLeftProduct f405desc1IntegerForm
    f406rawM4Form f405desc1 f405desc1Form f406_raw_integer_check hD hV hY hF

theorem f405desc1_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f405basis b405relative
    f406basis f405desc1 f406rawM4Form f405desc1Form
    f405desc1_actual f406_actual_raw_M4_matrix f405desc1_compression_check x y


#print axioms f405desc1_compression_check
#print axioms f405desc1_source_form
end TorusLean.BosonFiniteCertificate
