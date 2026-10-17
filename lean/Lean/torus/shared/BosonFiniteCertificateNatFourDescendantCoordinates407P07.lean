import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate407

/-! True all-level COM descendant coordinates, independently of any M4
form matrix. These columns are built from the original relative columns
using already proved actions of the genuine Nat COM raising operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f407desc0 : Matrix (Fin 11) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (-7/20), (7/15);
    (9/20), (-4/15);
    (-1/4), 0;
    (3/5), (-17/15);
    (-3/2), (4/3);
    1, 0;
    0, (-1/3);
    0, 1;
    0, (-2);
    0, 1]

theorem f407desc0_root : f407desc0=b407relative := by
  decide +kernel

theorem f407desc0_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f407desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f407desc0_root]

#print axioms f407desc0_root
#print axioms f407desc0_actual
end TorusLean.BosonFiniteCertificate
