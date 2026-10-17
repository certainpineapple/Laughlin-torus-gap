import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger405
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
import torus.shared.BosonFiniteCertificate404

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

def f404desc1Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(-38287784058142548191850659/2250000000000000000000000), (81469768913880843118579877/2250000000000000000000000);
    (81469768913880843118579877/2250000000000000000000000), (-96906072914331889600113779/2250000000000000000000000)]

private def f404desc1IntegerCoordinates : Matrix (Fin 6) (Fin 2) ℤ :=
  !![1, (-1);
    (-1), 1;
    2, 4;
    (-8), 2;
    6, (-12);
    0, 6]

private def f404desc1IntegerLeftProduct : Matrix (Fin 2) (Fin 6) ℤ :=
  !![(-193910518663676378423281296), (-44725621574559479332772980), 34412420519501545592370856, 16945107624126674015987320, 10461630135092834544377088, 21782307143543492919146364;
    173935590142025551074735312, 1841455398532968633024460, (-39527828570574915404614600), (-36840332464078316893023736), (-10313676943240985717058672), (-17917050170378418193157076)]

private def f404desc1IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(-153151136232570192767402636), 325879075655523372474319508;
    325879075655523372474319508, (-387624291657327558400455116)]

theorem f404desc1_compression_check :
    f404desc1ᵀ*f405rawM4Form*f404desc1=f404desc1Form := by
  have hD : natFourIntegerMatrix 3 f404desc1IntegerCoordinates=f404desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc1IntegerCoordinates) (f404desc1) (by decide +kernel) a b
  have hV : f404desc1IntegerCoordinatesᵀ*f405rawInteger=f404desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 6) => (f404desc1IntegerCoordinatesᵀ*f405rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 6) => (f404desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 6) => (f404desc1IntegerCoordinatesᵀ*f405rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 6) => (f404desc1IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc1IntegerLeftProduct*f404desc1IntegerCoordinates=f404desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc1IntegerLeftProduct*f404desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc1IntegerLeftProduct*f404desc1IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc1IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc1IntegerForm=f404desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc1IntegerForm) (f404desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f405rawInteger f404desc1IntegerCoordinates f404desc1IntegerLeftProduct f404desc1IntegerForm
    f405rawM4Form f404desc1 f404desc1Form f405_raw_integer_check hD hV hY hF

theorem f404desc1_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f404basis b404relative
    f405basis f404desc1 f405rawM4Form f404desc1Form
    f404desc1_actual f405_actual_raw_M4_matrix f404desc1_compression_check x y


#print axioms f404desc1_compression_check
#print axioms f404desc1_source_form
end TorusLean.BosonFiniteCertificate
