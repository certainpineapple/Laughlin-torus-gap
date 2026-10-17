import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate413

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

def f413desc0 : Matrix (Fin 39) (Fin 5) ℚ :=
  !![(-1/924), (1/792), (1/792), (-1/495), (-1/495);
    (13/924), (-13/792), (-13/792), (13/495), (13/495);
    (-9/154), (41/924), (101/2772), (-4/77), (-7/165);
    (1/6), (-4/63), (-1/18), (17/315), (19/630);
    (-25/84), (25/504), (25/504), (-1/45), (-1/126);
    (9/28), (-1/56), (-1/56), 0, 0;
    (-1/7), 0, 0, 0, 0;
    (-2/77), (25/462), (43/693), (-122/1155), (-19/165);
    (1/7), (-25/84), (-59/252), (43/105), (79/210);
    (-10/21), (55/126), (5/14), (-142/315), (-17/63);
    (15/14), (-5/14), (-5/14), (1/5), (1/14);
    (-12/7), (1/7), (1/7), 0, 0;
    1, 0, 0, 0, 0;
    0, (5/12), (5/36), (-2/5), (-13/42);
    0, (-5/4), (-25/84), (33/35), (31/70);
    0, (15/14), (5/14), (-16/35), (-4/35);
    0, (-1/2), (-1/6), 0, 0;
    0, (20/21), 0, (-64/105), (-16/105);
    0, (-5/3), 0, (2/3), (1/15);
    0, 1, 0, 0, 0;
    0, 0, 0, (-1/5), 0;
    0, 0, (-1/14), (4/35), (6/35);
    0, 0, (5/14), (-4/7), (-6/7);
    0, 0, (-25/42), (24/35), (22/35);
    0, 0, (5/7), (-12/35), (-6/35);
    0, 0, (-1/3), 0, 0;
    0, 0, (-5/14), (27/35), (51/35);
    0, 0, (20/21), (-72/35), (-76/35);
    0, 0, (-5/3), (6/5), (3/5);
    0, 0, 1, 0, 0;
    0, 0, 0, (8/5), (4/5);
    0, 0, 0, (-12/5), (-2/5);
    0, 0, 0, 1, 0;
    0, 0, 0, 0, (-6/7);
    0, 0, 0, 0, 2;
    0, 0, 0, 0, (-3/5);
    0, 0, 0, 0, (-8/5);
    0, 0, 0, 0, 1;
    0, 0, 0, 0, 0]

theorem f413desc0_root : f413desc0=b413relative := by
  decide +kernel

theorem f413desc0_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f413basis (complexify b413relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f413desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f413desc0_root]

#print axioms f413desc0_root
#print axioms f413desc0_actual
end TorusLean.BosonFiniteCertificate
