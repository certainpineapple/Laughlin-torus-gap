import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates411P11

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

def f411desc1 : Matrix (Fin 34) (Fin 4) ℚ :=
  !![(1/252), (-1/210), (-1/210), (1/120);
    (-2/63), (4/105), (4/105), (-1/15);
    (2/21), (-2/35), (-1/35), (3/140);
    (-10/63), (-1/105), (-1/105), (1/15);
    (5/84), (1/14), (3/70), (-13/280);
    (4/21), (-1/35), (-1/35), 0;
    (-1/6), 0, 0, 0;
    (-1/126), (-1/21), (-8/105), (17/105);
    (5/63), (17/105), (-1/105), (4/105);
    0, (1/5), (1/5), (-3/5);
    0, (-19/35), (-11/35), (13/35);
    0, (1/5), (1/5), 0;
    (-5/14), (-6/35), (8/35), (-3/10);
    (20/21), (-2/5), (-22/35), (36/35);
    (-5/3), (8/5), (2/5), (-1/2);
    1, (-3/5), (-1/5), 0;
    0, (2/5), (2/5), (-2/5);
    0, (-9/5), (-1/5), (1/5);
    0, 1, 0, 0;
    (5/63), (-16/105), (2/105), (-11/105);
    (-5/14), (24/35), (11/35), (-3/7);
    (20/21), (-24/35), (-16/35), (48/35);
    (-5/3), (1/5), (3/5), (-4/5);
    1, 0, (-2/5), 0;
    0, (-6/7), (-38/35), (57/35);
    0, 2, 2, (-24/5);
    0, (-3/5), (-3/5), (12/5);
    0, (-8/5), (-8/5), 2;
    0, 1, 1, (-1);
    0, 0, (4/5), (-6/5);
    0, 0, (-8/5), (21/5);
    0, 0, 1, (-9/4);
    0, 0, 0, (-2);
    0, 0, 0, 1]

theorem f411desc1_step : f411raise*f411desc0=f411desc1 := by
  refine natFourSparseRowProduct_matrix_check f411raise f411desc0 f411desc1
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 0) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 1) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 2) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 3) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 4) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 5) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 6) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 7) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 8) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 9) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 10) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 11) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 12) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 13) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 14) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 15) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 16) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 17) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 18) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 19) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 20) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 21) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 22) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 23) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 24) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 25) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 26) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 27) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 28) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 29) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 30) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 31) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 32) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 33) f411desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc1 33 b)
      (by decide +kernel) 0 b

theorem f411desc1_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f411basis (complexify b411relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f411desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f411basis (complexify b411relative *ᵥ x))
    f411basis f412basis f411desc0 f411desc1 f411raise
    f411desc0_actual f411_actual_raise_block f411desc1_step x

def f411desc2 : Matrix (Fin 39) (Fin 4) ℚ :=
  !![(1/252), (-1/210), (-1/210), (1/120);
    (-5/252), (1/42), (1/42), (-1/24);
    (4/63), (-2/105), (1/105), (-19/420);
    (-4/63), (-1/15), (-4/105), (37/420);
    (-25/252), (13/210), (1/30), (17/840);
    (1/4), (3/70), (1/70), (-13/280);
    (-1/7), (-1/35), (-1/35), 0;
    (-1/14), (1/35), 0, (1/35);
    (16/63), (-1/21), (-23/105), (17/42);
    (-5/21), (12/35), (6/35), (-3/7);
    (5/42), (-1/5), (-1/35), (-9/28);
    (8/21), (-2/5), (-6/35), (13/35);
    (-1/3), (1/5), (1/5), 0;
    (-5/18), (-1/105), (23/105), (-11/42);
    (5/21), (-19/35), (1/35), (-6/35);
    (-5/7), (23/35), (-19/35), (9/10);
    (1/3), (3/5), (1/5), (-1/2);
    (20/21), 0, (-8/35), (22/35);
    (-5/3), (3/5), 1, (-11/10);
    1, (-12/5), (-2/5), (1/5);
    0, (6/5), (-1/5), (1/5);
    (1/14), (-1/5), (-2/35), (2/35);
    (-5/126), (41/105), (38/105), (-74/105);
    (25/42), (1/5), (2/35), (12/35);
    (-5/7), (-36/35), (-6/35), (33/35);
    (1/3), (2/5), 0, (-4/5);
    (-15/14), (12/35), (-8/35), (33/70);
    (20/7), (-52/35), (-12/7), (78/35);
    (-5), (17/5), 3, (-9/2);
    3, (-6/5), (-8/5), (12/5);
    0, (4/5), (4/5), (-16/5);
    0, (-18/5), (-2), (23/5);
    0, 2, 1, (-1);
    0, (-6/7), (-2/7), (3/7);
    0, 2, (14/5), (-21/5);
    0, (-3/5), (-1/5), (21/10);
    0, (-8/5), (-24/5), (42/5);
    0, 1, 3, (-19/2);
    0, 0, 0, 2]

theorem f411desc2_step : f412raise*f411desc1=f411desc2 := by
  refine natFourSparseRowProduct_matrix_check f412raise f411desc1 f411desc2
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 0) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 1) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 2) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 3) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 4) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 5) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 6) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 7) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 8) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 9) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 10) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 11) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 12) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 13) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 14) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 15) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 16) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 17) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 18) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 19) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 20) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 21) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 22) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 23) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 24) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 25) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 26) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 27) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 28) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 29) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 30) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 31) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 32) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 33) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 34) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 35) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 36) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 37) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 38) f411desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc2 38 b)
      (by decide +kernel) 0 b

theorem f411desc2_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f411basis (complexify b411relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f411desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f411basis (complexify b411relative *ᵥ x))
    f412basis f413basis f411desc1 f411desc2 f412raise
    f411desc1_actual f412_actual_raise_block f411desc2_step x

#print axioms f411desc1_step
#print axioms f411desc1_actual
#print axioms f411desc2_step
#print axioms f411desc2_actual
end TorusLean.BosonFiniteCertificate
