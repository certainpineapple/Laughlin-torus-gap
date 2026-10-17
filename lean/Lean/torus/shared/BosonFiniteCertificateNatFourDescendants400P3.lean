import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger403
import torus.shared.BosonFiniteCertificateNatFourRaise400
import torus.shared.BosonFiniteCertificateNatFourRaise401
import torus.shared.BosonFiniteCertificateNatFourRaise402
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
import torus.shared.BosonFiniteCertificate400

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

def f400desc3Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(19455720270858974146461057/1953125000000000000000)]

private def f400desc3IntegerCoordinates : Matrix (Fin 3) (Fin 1) ℤ :=
  !![4;
    36;
    24]

private def f400desc3IntegerLeftProduct : Matrix (Fin 1) (Fin 3) ℤ :=
  !![180499744227110977119893904, 116366193912148478098878672, 210422784205583568456202224]

private def f400desc3IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![9961328778679794762988061184]

theorem f400desc3_compression_check :
    f400desc3ᵀ*f403rawM4Form*f400desc3=f400desc3Form := by
  have hD : natFourIntegerMatrix 1 f400desc3IntegerCoordinates=f400desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc3IntegerCoordinates) (f400desc3) (by decide +kernel) a b
  have hV : f400desc3IntegerCoordinatesᵀ*f403rawInteger=f400desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f400desc3IntegerCoordinatesᵀ*f403rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f400desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc3IntegerLeftProduct*f400desc3IntegerCoordinates=f400desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc3IntegerLeftProduct*f400desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc3IntegerForm=f400desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc3IntegerForm) (f400desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f403rawInteger f400desc3IntegerCoordinates f400desc3IntegerLeftProduct f400desc3IntegerForm
    f403rawM4Form f400desc3 f400desc3Form f403_raw_integer_check hD hV hY hF

theorem f400desc3_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f400basis b400relative
    f403basis f400desc3 f403rawM4Form f400desc3Form
    f400desc3_actual f403_actual_raw_M4_matrix f400desc3_compression_check x y


#print axioms f400desc3_compression_check
#print axioms f400desc3_source_form
end TorusLean.BosonFiniteCertificate
