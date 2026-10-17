import torus.shared.BosonFiniteCertificateNatFourRaiseSparse409
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate409

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

def f409desc0 : Matrix (Fin 18) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (9/70), (-9/56), (-9/56);
    (-2/7), (9/35), (11/70);
    (2/5), (-3/20), (-1/20);
    (-1/5), 0, 0;
    (-8/35), (27/70), (17/35);
    (4/5), (-27/20), (-19/20);
    (-8/5), (9/10), (3/10);
    1, 0, 0;
    0, (27/20), (9/20);
    0, (-9/4), (-1/4);
    0, 1, 0;
    0, 0, (-1/2);
    0, 0, (3/2);
    0, 0, (-1/2);
    0, 0, (-3/2);
    0, 0, 1;
    0, 0, 0]

theorem f409desc0_root : f409desc0=b409relative := by
  decide +kernel

theorem f409desc0_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f409desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f409desc0_root]

def f409desc1 : Matrix (Fin 23) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (3/35), (-3/28), (-3/28);
    (-11/70), (27/280), (-1/280);
    (4/35), (3/28), (3/28);
    (1/5), (-3/20), (-1/20);
    (-1/5), 0, 0;
    (1/35), (9/140), (23/140);
    (-8/35), (-9/140), (47/140);
    0, (-3/4), (-3/4);
    0, (9/10), (3/10);
    (4/5), 0, (-1/2);
    (-8/5), (27/20), (19/20);
    1, (-9/4), (-1/4);
    0, (3/4), (-1/4);
    (-8/35), (27/70), (-1/70);
    (4/5), (-27/20), (-19/20);
    (-8/5), (9/10), (13/10);
    1, 0, (-1/2);
    0, (27/20), (39/20);
    0, (-9/4), (-9/4);
    0, 1, 1;
    0, 0, (-3/2);
    0, 0, 1]

theorem f409desc1_step : f409raise*f409desc0=f409desc1 := by
  refine natFourSparseRowProduct_matrix_check f409raise f409desc0 f409desc1
    f409raiseSparseRows f409_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 0) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 1) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 2) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 3) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 4) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 5) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 6) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 7) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 8) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 9) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 10) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 11) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 12) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 13) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 14) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 15) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 16) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 17) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 18) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 19) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 20) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 21) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 22) f409desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc1 22 b)
      (by decide +kernel) 0 b

theorem f409desc1_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f409desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f409basis (complexify b409relative *ᵥ x))
    f409basis f410basis f409desc0 f409desc1 f409raise
    f409desc0_actual f409_actual_raise_block f409desc1_step x

def f409desc2 : Matrix (Fin 27) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (3/70), (-3/56), (-3/56);
    (-1/14), (-3/280), (-31/280);
    (-3/70), (57/280), (29/280);
    (11/35), (-3/70), (2/35);
    (-1/5), (-3/20), (-1/20);
    (1/5), (-3/20), (-1/20);
    (-17/35), (9/35), (23/35);
    0, (-3/5), (-1/5);
    (2/5), (-3/20), (-11/20);
    (-2/5), (9/10), (3/10);
    (4/7), (-9/140), (-23/140);
    0, (3/5), (-4/5);
    (2/5), (-9/4), (3/4);
    (-8/5), (21/10), (7/10);
    1, (-3/4), (-3/4);
    (-1/5), (9/20), (3/20);
    (-4/35), (-9/35), (-23/35);
    (-4/5), (-6/5), (-2/5);
    (2/5), (9/5), (3/5);
    (12/5), (-27/20), (-9/20);
    (-24/5), (18/5), (26/5);
    3, (-9/2), (-7/2);
    0, (3/2), (1/2);
    0, (27/20), (9/20);
    0, (-9/4), (-19/4);
    0, 1, 3]

theorem f409desc2_step : f410raise*f409desc1=f409desc2 := by
  refine natFourSparseRowProduct_matrix_check f410raise f409desc1 f409desc2
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 0) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 1) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 2) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 3) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 4) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 5) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 6) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 7) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 8) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 9) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 10) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 11) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 12) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 13) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 14) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 15) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 16) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 17) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 18) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 19) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 20) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 21) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 22) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 23) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 24) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 25) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 26) f409desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc2 26 b)
      (by decide +kernel) 0 b

theorem f409desc2_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f409desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f409basis (complexify b409relative *ᵥ x))
    f410basis f411basis f409desc1 f409desc2 f410raise
    f409desc1_actual f410_actual_raise_block f409desc2_step x

#print axioms f409desc0_root
#print axioms f409desc0_actual
#print axioms f409desc1_step
#print axioms f409desc1_actual
#print axioms f409desc2_step
#print axioms f409desc2_actual
end TorusLean.BosonFiniteCertificate
