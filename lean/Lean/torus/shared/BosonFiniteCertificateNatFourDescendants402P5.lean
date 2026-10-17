import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger407
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

def f402desc5Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(36312670203361236698537973541/62500000000000000000000)]

private def f402desc5IntegerCoordinates : Matrix (Fin 11) (Fin 1) ℤ :=
  !![(-1);
    (-13);
    (-23);
    (-25);
    (-38);
    (-70);
    (-20);
    10;
    (-10);
    100;
    90]

private def f402desc5IntegerLeftProduct : Matrix (Fin 1) (Fin 11) ℤ :=
  !![8207405483949798579121190400, (-394513509667457015937560280), (-2494951922106554740069709312), (-921075330862735614672908712), (-2740824320151373869684119040), (-957514602438309106422867952), 481475105989723242964365696, 880380741836483523826133672, 74889579589358698990697400, 1572652916670288442361632800, 1964473645843266922636520472]

private def f402desc5IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![581002723253779787176607576656]

theorem f402desc5_compression_check :
    f402desc5ᵀ*f407rawM4Form*f402desc5=f402desc5Form := by
  have hD : natFourIntegerMatrix 1 f402desc5IntegerCoordinates=f402desc5 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc5IntegerCoordinates) (f402desc5) (by decide +kernel) a b
  have hV : f402desc5IntegerCoordinatesᵀ*f407rawInteger=f402desc5IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f402desc5IntegerCoordinatesᵀ*f407rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f402desc5IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc5IntegerLeftProduct*f402desc5IntegerCoordinates=f402desc5IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc5IntegerLeftProduct*f402desc5IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc5IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc5IntegerForm=f402desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc5IntegerForm) (f402desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f407rawInteger f402desc5IntegerCoordinates f402desc5IntegerLeftProduct f402desc5IntegerForm
    f407rawM4Form f402desc5 f402desc5Form f407_raw_integer_check hD hV hY hF

theorem f402desc5_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f402basis b402relative
    f407basis f402desc5 f407rawM4Form f402desc5Form
    f402desc5_actual f407_actual_raw_M4_matrix f402desc5_compression_check x y


#print axioms f402desc5_compression_check
#print axioms f402desc5_source_form
end TorusLean.BosonFiniteCertificate
