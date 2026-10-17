import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger406
import torus.shared.BosonFiniteCertificateNatFourRaise403
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
import torus.shared.BosonFiniteCertificate403

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

def f403desc3Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-85953430267148295326917179/125000000000000000000000)]

private def f403desc3IntegerCoordinates : Matrix (Fin 9) (Fin 1) ℤ :=
  !![1;
    6;
    (-3);
    (-6);
    6;
    (-24);
    (-6);
    8;
    18]

private def f403desc3IntegerLeftProduct : Matrix (Fin 1) (Fin 9) ℤ :=
  !![(-1703481474505908066202544544), (-557640815171563474729389336), (-221341225653794761732374384), (-105837470615179538316638928), (-40462400641218347148795552), (-77799575122115357816307408), (-54479337233848357600859760), (-9257528442886577884330992), (-48747949922743004344918944)]

private def f403desc3IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![(-2750509768548745450461349728)]

theorem f403desc3_compression_check :
    f403desc3ᵀ*f406rawM4Form*f403desc3=f403desc3Form := by
  have hD : natFourIntegerMatrix 2 f403desc3IntegerCoordinates=f403desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc3IntegerCoordinates) (f403desc3) (by decide +kernel) a b
  have hV : f403desc3IntegerCoordinatesᵀ*f406rawInteger=f403desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f403desc3IntegerCoordinatesᵀ*f406rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f403desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc3IntegerLeftProduct*f403desc3IntegerCoordinates=f403desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc3IntegerLeftProduct*f403desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc3IntegerForm=f403desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc3IntegerForm) (f403desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f406rawInteger f403desc3IntegerCoordinates f403desc3IntegerLeftProduct f403desc3IntegerForm
    f406rawM4Form f403desc3 f403desc3Form f406_raw_integer_check hD hV hY hF

theorem f403desc3_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f403basis b403relative
    f406basis f403desc3 f406rawM4Form f403desc3Form
    f403desc3_actual f406_actual_raw_M4_matrix f403desc3_compression_check x y


#print axioms f403desc3_compression_check
#print axioms f403desc3_source_form
end TorusLean.BosonFiniteCertificate
