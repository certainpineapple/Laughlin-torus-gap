import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate411

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

def f411desc0 : Matrix (Fin 27) (Fin 4) ℚ :=
  !![(1/252), (-1/210), (-1/210), (1/120);
    (-11/252), (11/210), (11/210), (-11/120);
    (5/36), (-23/210), (-17/210), (19/168);
    (-25/84), (1/10), (1/14), (-13/280);
    (5/14), (-1/35), (-1/35), 0;
    (-1/6), 0, 0, 0;
    (5/63), (-16/105), (-19/105), (29/84);
    (-5/14), (24/35), (18/35), (-123/140);
    (20/21), (-24/35), (-16/35), (13/35);
    (-5/3), (1/5), (1/5), 0;
    1, 0, 0, 0;
    0, (-6/7), (-2/7), (81/140);
    0, 2, (2/5), (-1/2);
    0, (-3/5), (-1/5), 0;
    0, (-8/5), 0, (1/10);
    0, 1, 0, 0;
    0, 0, (1/5), (-9/20);
    0, 0, (-4/5), (9/5);
    0, 0, (4/5), (-4/5);
    0, 0, (-2/5), 0;
    0, 0, (4/5), (-51/20);
    0, 0, (-8/5), (12/5);
    0, 0, 1, 0;
    0, 0, 0, (-1/2);
    0, 0, 0, (27/20);
    0, 0, 0, (-9/4);
    0, 0, 0, 1]

theorem f411desc0_root : f411desc0=b411relative := by
  decide +kernel

theorem f411desc0_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f411basis (complexify b411relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f411desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f411desc0_root]

#print axioms f411desc0_root
#print axioms f411desc0_actual
end TorusLean.BosonFiniteCertificate
