import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger405
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
import torus.shared.BosonFiniteCertificate402

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

def f402desc3Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(347618943634000621666651541/250000000000000000000000)]

private def f402desc3IntegerCoordinates : Matrix (Fin 6) (Fin 1) ℤ :=
  !![(-1);
    (-7);
    (-6);
    (-4);
    6;
    12]

private def f402desc3IntegerLeftProduct : Matrix (Fin 1) (Fin 6) ℤ :=
  !![393861376060364114648520336, (-19079383588089161724714108), 17354327048822649142192408, 21250436290094639183577736, 46541076529969037540256544, 130055226146103557965671156]

private def f402desc3IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1390475774536002486666606164]

theorem f402desc3_compression_check :
    f402desc3ᵀ*f405rawM4Form*f402desc3=f402desc3Form := by
  have hD : natFourIntegerMatrix 1 f402desc3IntegerCoordinates=f402desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc3IntegerCoordinates) (f402desc3) (by decide +kernel) a b
  have hV : f402desc3IntegerCoordinatesᵀ*f405rawInteger=f402desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 6) => (f402desc3IntegerCoordinatesᵀ*f405rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 6) => (f402desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc3IntegerLeftProduct*f402desc3IntegerCoordinates=f402desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc3IntegerLeftProduct*f402desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc3IntegerForm=f402desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc3IntegerForm) (f402desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f405rawInteger f402desc3IntegerCoordinates f402desc3IntegerLeftProduct f402desc3IntegerForm
    f405rawM4Form f402desc3 f402desc3Form f405_raw_integer_check hD hV hY hF

theorem f402desc3_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f402basis b402relative
    f405basis f402desc3 f405rawM4Form f402desc3Form
    f402desc3_actual f405_actual_raw_M4_matrix f402desc3_compression_check x y


#print axioms f402desc3_compression_check
#print axioms f402desc3_source_form
end TorusLean.BosonFiniteCertificate
