import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
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

def f402desc6Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(18334751747640905597161769379/1953125000000000000000)]

private def f402desc6IntegerCoordinates : Matrix (Fin 15) (Fin 1) ℤ :=
  !![(-1);
    (-16);
    (-36);
    (-48);
    (-25);
    (-64);
    (-192);
    (-160);
    (-60);
    0;
    (-48);
    0;
    80;
    480;
    90]

private def f402desc6IntegerLeftProduct : Matrix (Fin 1) (Fin 15) ℤ :=
  !![18604214567352624348024433920, (-3254589306884816042795933760), (-15145679089395050158078749888), (-3499212083787543808025460192), (-22201709907203875631802668544), (-11477196880319163070670448000), (-11145995146587615077547468672), (-4256072936784334948604585472), (-4146019376653678080428633088), 4289159238770988792906642048, (-9691488578704095206241445440), 5494239469804841556659328, 6822543009369303671362713984, 6510389429382211931962769664, 1615422065871700390819792896]

private def f402desc6IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![9387392894792143665746825922048]

theorem f402desc6_compression_check :
    f402desc6ᵀ*f408rawM4Form*f402desc6=f402desc6Form := by
  have hD : natFourIntegerMatrix 1 f402desc6IntegerCoordinates=f402desc6 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc6IntegerCoordinates) (f402desc6) (by decide +kernel) a b
  have hV : f402desc6IntegerCoordinatesᵀ*f408rawInteger=f402desc6IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f402desc6IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f402desc6IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc6IntegerLeftProduct*f402desc6IntegerCoordinates=f402desc6IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc6IntegerLeftProduct*f402desc6IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc6IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc6IntegerForm=f402desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc6IntegerForm) (f402desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f408rawInteger f402desc6IntegerCoordinates f402desc6IntegerLeftProduct f402desc6IntegerForm
    f408rawM4Form f402desc6 f402desc6Form f408_raw_integer_check hD hV hY hF

theorem f402desc6_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f402basis b402relative
    f408basis f402desc6 f408rawM4Form f402desc6Form
    f402desc6_actual f408_actual_raw_M4_matrix f402desc6_compression_check x y


#print axioms f402desc6_compression_check
#print axioms f402desc6_source_form
end TorusLean.BosonFiniteCertificate
