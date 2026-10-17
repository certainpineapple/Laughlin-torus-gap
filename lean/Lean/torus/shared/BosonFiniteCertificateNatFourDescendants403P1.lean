import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger404
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

def f403desc1Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-117689008474984306105683/5000000000000000000000)]

private def f403desc1IntegerCoordinates : Matrix (Fin 5) (Fin 1) ℤ :=
  !![1;
    0;
    (-3);
    0;
    2]

private def f403desc1IntegerLeftProduct : Matrix (Fin 1) (Fin 5) ℤ :=
  !![(-56835596128830898469179824), (-2754842243872635325481676), 8201085035918489169427152, 3731319110477759819084976, (-6356177771700539453542560)]

private def f403desc1IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![(-94151206779987444884546400)]

theorem f403desc1_compression_check :
    f403desc1ᵀ*f404rawM4Form*f403desc1=f403desc1Form := by
  have hD : natFourIntegerMatrix 2 f403desc1IntegerCoordinates=f403desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc1IntegerCoordinates) (f403desc1) (by decide +kernel) a b
  have hV : f403desc1IntegerCoordinatesᵀ*f404rawInteger=f403desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f403desc1IntegerCoordinatesᵀ*f404rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f403desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc1IntegerLeftProduct*f403desc1IntegerCoordinates=f403desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc1IntegerLeftProduct*f403desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc1IntegerForm=f403desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc1IntegerForm) (f403desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f404rawInteger f403desc1IntegerCoordinates f403desc1IntegerLeftProduct f403desc1IntegerForm
    f404rawM4Form f403desc1 f403desc1Form f404_raw_integer_check hD hV hY hF

theorem f403desc1_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f403basis b403relative
    f404basis f403desc1 f404rawM4Form f403desc1Form
    f403desc1_actual f404_actual_raw_M4_matrix f403desc1_compression_check x y


#print axioms f403desc1_compression_check
#print axioms f403desc1_source_form
end TorusLean.BosonFiniteCertificate
