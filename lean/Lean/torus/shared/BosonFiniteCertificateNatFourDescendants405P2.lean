import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger407
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

def f405desc2Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-12878657632948057320589707/250000000000000000000000)]

private def f405desc2IntegerCoordinates : Matrix (Fin 11) (Fin 1) ℤ :=
  !![(-1);
    (-1);
    5;
    (-1);
    6;
    2;
    (-12);
    10;
    (-6);
    (-20);
    18]

private def f405desc2IntegerLeftProduct : Matrix (Fin 1) (Fin 11) ℤ :=
  !![3010657516979229590698993536, 863694887312289533450950632, (-1174462170171224354129792), 232988097719596083174568344, 217841238905234428987797504, (-49140719413124421154776880), 52608997952169134621793600, (-50152439098843131708219448), 27126759072085099786170936, (-81352055467303521454233728), 39915107256288580304948952]

private def f405desc2IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![(-1854526699144520254164917808)]

theorem f405desc2_compression_check :
    f405desc2ᵀ*f407rawM4Form*f405desc2=f405desc2Form := by
  have hD : natFourIntegerMatrix 6 f405desc2IntegerCoordinates=f405desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc2IntegerCoordinates) (f405desc2) (by decide +kernel) a b
  have hV : f405desc2IntegerCoordinatesᵀ*f407rawInteger=f405desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f405desc2IntegerCoordinatesᵀ*f407rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f405desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc2IntegerLeftProduct*f405desc2IntegerCoordinates=f405desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc2IntegerLeftProduct*f405desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc2IntegerForm=f405desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc2IntegerForm) (f405desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f407rawInteger f405desc2IntegerCoordinates f405desc2IntegerLeftProduct f405desc2IntegerForm
    f407rawM4Form f405desc2 f405desc2Form f407_raw_integer_check hD hV hY hF

theorem f405desc2_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f405basis b405relative
    f407basis f405desc2 f407rawM4Form f405desc2Form
    f405desc2_actual f407_actual_raw_M4_matrix f405desc2_compression_check x y


#print axioms f405desc2_compression_check
#print axioms f405desc2_source_form
end TorusLean.BosonFiniteCertificate
