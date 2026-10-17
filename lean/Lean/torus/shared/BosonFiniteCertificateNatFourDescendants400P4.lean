import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger404
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

def f400desc4Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(17810937718828961893396551/122070312500000000000)]

private def f400desc4IntegerCoordinates : Matrix (Fin 5) (Fin 1) ℤ :=
  !![4;
    48;
    36;
    144;
    24]

private def f400desc4IntegerLeftProduct : Matrix (Fin 1) (Fin 5) ℤ :=
  !![443398906734529453059776256, (-65086244296105107500338608), 648288443289917136833464128, 708726761405166825772476096, 910946178797530972551684480]

private def f400desc4IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![145907201792646855830704545792]

theorem f400desc4_compression_check :
    f400desc4ᵀ*f404rawM4Form*f400desc4=f400desc4Form := by
  have hD : natFourIntegerMatrix 1 f400desc4IntegerCoordinates=f400desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc4IntegerCoordinates) (f400desc4) (by decide +kernel) a b
  have hV : f400desc4IntegerCoordinatesᵀ*f404rawInteger=f400desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f400desc4IntegerCoordinatesᵀ*f404rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f400desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc4IntegerLeftProduct*f400desc4IntegerCoordinates=f400desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc4IntegerLeftProduct*f400desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc4IntegerForm=f400desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc4IntegerForm) (f400desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f404rawInteger f400desc4IntegerCoordinates f400desc4IntegerLeftProduct f400desc4IntegerForm
    f404rawM4Form f400desc4 f400desc4Form f404_raw_integer_check hD hV hY hF

theorem f400desc4_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f400basis b400relative
    f404basis f400desc4 f404rawM4Form f400desc4Form
    f400desc4_actual f404_actual_raw_M4_matrix f400desc4_compression_check x y


#print axioms f400desc4_compression_check
#print axioms f400desc4_source_form
end TorusLean.BosonFiniteCertificate
