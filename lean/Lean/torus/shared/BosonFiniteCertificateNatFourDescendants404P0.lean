import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger404
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

def f404desc0Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1165877188316444383800919/140625000000000000000000), (1082832276167718545634779/562500000000000000000000);
    (1082832276167718545634779/562500000000000000000000), (-1522009244978652907822093/281250000000000000000000)]

private def f404desc0IntegerCoordinates : Matrix (Fin 5) (Fin 2) ℤ :=
  !![1, (-1);
    (-4), 4;
    3, 0;
    0, (-6);
    0, 3]

private def f404desc0IntegerLeftProduct : Matrix (Fin 2) (Fin 5) ℤ :=
  !![1105364516923385872032288, (-658443434749409175675724), 23625667265443805996174544, 8628923862688365730231312, 24279332616911571228759840;
    (-597329354291262182390640), (-12284936351534164977149060), (-10405699877720633665349712), (-6538017811296032176368832), (-13129995551749229460771456)]

private def f404desc0IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![74616140052252440563258816, 17325316418683496730156464;
    17325316418683496730156464, (-48704295839316893050306976)]

theorem f404desc0_compression_check :
    f404desc0ᵀ*f404rawM4Form*f404desc0=f404desc0Form := by
  have hD : natFourIntegerMatrix 3 f404desc0IntegerCoordinates=f404desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc0IntegerCoordinates) (f404desc0) (by decide +kernel) a b
  have hV : f404desc0IntegerCoordinatesᵀ*f404rawInteger=f404desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f404desc0IntegerCoordinatesᵀ*f404rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f404desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f404desc0IntegerCoordinatesᵀ*f404rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f404desc0IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc0IntegerLeftProduct*f404desc0IntegerCoordinates=f404desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc0IntegerLeftProduct*f404desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc0IntegerLeftProduct*f404desc0IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc0IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc0IntegerForm=f404desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc0IntegerForm) (f404desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f404rawInteger f404desc0IntegerCoordinates f404desc0IntegerLeftProduct f404desc0IntegerForm
    f404rawM4Form f404desc0 f404desc0Form f404_raw_integer_check hD hV hY hF

theorem f404desc0_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f404basis b404relative
    f404basis f404desc0 f404rawM4Form f404desc0Form
    f404desc0_actual f404_actual_raw_M4_matrix f404desc0_compression_check x y


#print axioms f404desc0_compression_check
#print axioms f404desc0_source_form
end TorusLean.BosonFiniteCertificate
