import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates401
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaw405
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
import torus.shared.BosonFiniteCertificate401

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

def f401desc4Form : Matrix (Fin 0) (Fin 0) ℚ :=
  fun _ _ => 0

private def f401desc4IntegerCoordinates : Matrix (Fin 6) (Fin 0) ℤ :=
  fun _ _ => 0

private def f401desc4IntegerLeftProduct : Matrix (Fin 0) (Fin 6) ℤ :=
  fun _ _ => 0

private def f401desc4IntegerForm : Matrix (Fin 0) (Fin 0) ℤ :=
  fun _ _ => 0

theorem f401desc4_compression_check :
    f401desc4ᵀ*f405rawM4Form*f401desc4=f401desc4Form := by
  ext a b
  exact Fin.elim0 a

theorem f401desc4_source_form (x y : Fin 0 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f401basis (complexify b401relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f401basis (complexify b401relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f401desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f401basis b401relative
    f405basis f401desc4 f405rawM4Form f401desc4Form
    f401desc4_actual f405_actual_raw_M4_matrix f401desc4_compression_check x y


#print axioms f401desc4_compression_check
#print axioms f401desc4_source_form
end TorusLean.BosonFiniteCertificate
