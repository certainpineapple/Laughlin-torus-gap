import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger405
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

def f405desc0Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-168228195312546119714822827/9000000000000000000000000)]

private def f405desc0IntegerCoordinates : Matrix (Fin 6) (Fin 1) ℤ :=
  !![(-1);
    5;
    (-2);
    (-8);
    6;
    0]

private def f405desc0IntegerLeftProduct : Matrix (Fin 1) (Fin 6) ℤ :=
  !![104625954217290924898766352, (-27461818186605493186869180), 31889113316347293913395544, 38175092266832551716794440, (-10299795222085181077505408), (-8041411002535048365024396)]

private def f405desc0IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![(-672912781250184478859291308)]

theorem f405desc0_compression_check :
    f405desc0ᵀ*f405rawM4Form*f405desc0=f405desc0Form := by
  have hD : natFourIntegerMatrix 6 f405desc0IntegerCoordinates=f405desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc0IntegerCoordinates) (f405desc0) (by decide +kernel) a b
  have hV : f405desc0IntegerCoordinatesᵀ*f405rawInteger=f405desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 6) => (f405desc0IntegerCoordinatesᵀ*f405rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 6) => (f405desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc0IntegerLeftProduct*f405desc0IntegerCoordinates=f405desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc0IntegerLeftProduct*f405desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc0IntegerForm=f405desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc0IntegerForm) (f405desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f405rawInteger f405desc0IntegerCoordinates f405desc0IntegerLeftProduct f405desc0IntegerForm
    f405rawM4Form f405desc0 f405desc0Form f405_raw_integer_check hD hV hY hF

theorem f405desc0_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f405basis b405relative
    f405basis f405desc0 f405rawM4Form f405desc0Form
    f405desc0_actual f405_actual_raw_M4_matrix f405desc0_compression_check x y


#print axioms f405desc0_compression_check
#print axioms f405desc0_source_form
end TorusLean.BosonFiniteCertificate
