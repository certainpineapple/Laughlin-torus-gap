import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate414

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

def f414desc0 : Matrix (Fin 47) (Fin 8) ℚ :=
  !![(-1/1716), (1/1716), (-1/1287), (1/1716), (-1/1287), (-1/1287), (1/715), (1/715);
    (7/858), (-7/858), (14/1287), (-7/858), (14/1287), (14/1287), (-14/715), (-14/715);
    (-7/132), (9/308), (-43/1386), (25/924), (-17/693), (-31/1386), (2/55), (1/30);
    (7/33), (-16/231), (31/693), (-16/231), (13/396), (20/693), (-38/1155), (-9/385);
    (-7/12), (3/28), (-2/63), (3/28), (-1/42), (-1/42), (4/315), (1/210);
    (7/6), (-2/21), (1/126), (-2/21), (1/126), (1/126), 0, 0;
    (-7/4), (1/28), 0, (1/28), 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, (1/42), (-5/126), (2/77), (-32/693), (-67/1386), (1/11), (31/330);
    0, (-1/7), (5/21), (-9/77), (181/924), (2/11), (-26/77), (-127/385);
    0, (1/3), (-23/63), (1/3), (-67/252), (-2/9), (14/45), (5/21);
    0, (-25/42), (5/18), (-25/42), (25/126), (25/126), (-8/63), (-1/21);
    0, (9/14), (-1/14), (9/14), (-1/14), (-1/14), 0, 0;
    0, (-2/7), 0, (-2/7), 0, 0, 0, 0;
    0, (1/7), (-8/21), 0, (-4/21), (-17/126), (11/35), (3/10);
    0, (-10/21), (80/63), 0, (125/252), (5/21), (-62/105), (-47/105);
    0, (15/14), (-15/14), 0, (-5/14), (-5/21), (9/35), (3/35);
    0, (-12/7), (2/7), 0, (1/7), (2/21), 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, (-25/21), 0, (-25/84), 0, (2/7), (6/35);
    0, 0, (50/21), 0, (5/14), 0, (-4/15), (-2/35);
    0, 0, (-2/3), 0, (-1/6), 0, 0, 0;
    0, 0, (-5/3), 0, 0, 0, (1/15), 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, (-2/77), (25/462), (50/693), (-32/231), (-12/77);
    0, 0, 0, (1/7), (-25/84), (-25/63), (16/21), (6/7);
    0, 0, 0, (-10/21), (55/126), (10/21), (-32/45), (-68/105);
    0, 0, 0, (15/14), (-5/14), (-10/21), (11/35), (9/70);
    0, 0, 0, (-12/7), (1/7), (4/21), 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, (5/12), (40/63), (-48/35), (-58/35);
    0, 0, 0, 0, (-5/4), (-25/21), (18/7), (93/35);
    0, 0, 0, 0, (15/14), (10/7), (-44/35), (-18/35);
    0, 0, 0, 0, (-1/2), (-2/3), 0, 0;
    0, 0, 0, 0, (20/21), 0, (-128/105), (-8/7);
    0, 0, 0, 0, (-5/3), 0, (4/3), (2/5);
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, (-2/5), 0;
    0, 0, 0, 0, 0, (-5/14), (27/35), (81/70);
    0, 0, 0, 0, 0, (20/21), (-72/35), (-108/35);
    0, 0, 0, 0, 0, (-5/3), (6/5), (3/5);
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, (8/5), (16/5);
    0, 0, 0, 0, 0, 0, (-12/5), (-6/5);
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, (-8/5);
    0, 0, 0, 0, 0, 0, 0, 1]

theorem f414desc0_root : f414desc0=b414relative := by
  decide +kernel

theorem f414desc0_actual (x : Fin 8 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f414basis (complexify b414relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f414desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f414desc0_root]

#print axioms f414desc0_root
#print axioms f414desc0_actual
end TorusLean.BosonFiniteCertificate
