import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates410P11

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

def f410desc2 : Matrix (Fin 34) (Fin 5) ℚ :=
  !![(-1/126), (1/126), (1/126), (-1/84), (-1/84);
    (2/63), (-2/63), (-2/63), (1/21), (1/21);
    (-2/9), (1/45), (-2/315), (11/210), (17/210);
    (20/63), (26/315), (8/315), (-43/420), (-2/21);
    (-5/42), (-17/210), (-23/210), (1/140), (-9/140);
    (-8/21), (-2/105), (-2/105), (11/140), (1/35);
    (1/3), (1/15), (1/15), 0, 0;
    (17/63), (-22/315), (-13/315), (2/105), (-1/105);
    (-20/21), (16/105), (8/21), (-13/28), (-19/35);
    (50/21), (-8/21), (2/105), (9/28), (13/35);
    (-20/7), (2/35), (2/7), (5/28), (3/5);
    (4/3), (-2/15), (-2/15), (-11/20), (-1/5);
    (-5/7), (-3/35), (-3/7), (9/35), (1/5);
    (40/21), (52/105), (-44/105), (3/10), (18/35);
    (-10/3), (4/3), (14/15), (-4/5), (-1);
    2, (-2/5), (-4/5), (3/4), (1/5);
    0, (-4/5), (4/5), (-1/2), (-4/5);
    0, (-6/5), (-2/5), (3/4), (3/5);
    0, 1, 0, (-1/2), 0;
    (10/63), (76/315), (22/315), (-31/210), (-8/105);
    (-5/7), (-2/7), (-11/35), (93/140), (26/35);
    (40/21), (-32/105), (-8/15), (12/35), (-8/35);
    (-10/3), (14/15), (8/15), (-13/20), (-7/5);
    2, (-4/5), (-2/5), (9/10), (2/5);
    0, (-4/5), (4/35), (-3/70), (-2/35);
    0, (12/5), (4/5), (-39/10), (-14/5);
    0, (-2/5), (2/5), (21/20), (19/5);
    0, (-16/5), (-16/5), 4, 4;
    0, 2, 2, (-7/4), (-3);
    0, (4/5), (8/5), (-3/5), (-4/5);
    0, (-8/5), (-16/5), (24/5), 4;
    0, 1, 2, (-9/2), (-9/2);
    0, 0, 0, (-1), (-2);
    0, 0, 0, 1, 2]

theorem f410desc2_step : f411raise*f410desc1=f410desc2 := by
  refine natFourSparseRowProduct_matrix_check f411raise f410desc1 f410desc2
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 0) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 1) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 2) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 3) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 4) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 5) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 6) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 7) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 8) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 9) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 10) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 11) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 12) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 13) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 14) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 15) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 16) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 17) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 18) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 19) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 20) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 21) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 22) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 23) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 24) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 25) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 26) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 27) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 28) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 29) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 30) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 31) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 32) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f411raiseSparseRows 33) f410desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc2 33 b)
      (by decide +kernel) 0 b

theorem f410desc2_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f410desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f410basis (complexify b410relative *ᵥ x))
    f411basis f412basis f410desc1 f410desc2 f411raise
    f410desc1_actual f411_actual_raise_block f410desc2_step x

def f410desc3 : Matrix (Fin 39) (Fin 5) ℚ :=
  !![(-1/126), (1/126), (1/126), (-1/84), (-1/84);
    (1/126), (-1/126), (-1/126), (1/84), (1/84);
    (-4/21), (-1/105), (-4/105), (1/10), (9/70);
    (2/21), (11/105), (2/105), (-1/20), (-1/70);
    (25/126), (1/630), (-53/630), (-2/21), (-67/420);
    (-1/2), (-1/10), (-9/70), (3/35), (-1/28);
    (2/7), (4/35), (4/35), (11/140), (1/35);
    (1/3), (-2/15), (-11/105), (4/35), (3/35);
    (-6/7), (2/35), (2/7), (-9/28), (-2/5);
    (130/63), (-4/63), (142/315), (-73/210), (-38/105);
    (-5/7), (-17/35), (3/35), (18/35), (59/70);
    (-16/7), (-4/35), (4/35), (-3/14), (16/35);
    2, 0, 0, (-11/20), (-1/5);
    (-5/3), (1/15), (-1/21), (-29/140), (-12/35);
    (20/7), (-2/35), (-44/35), (159/140), (9/7);
    (-30/7), (66/35), (4/5), (-9/28), (4/35);
    2, (2/5), (-4/5), (3/20), (-4/5);
    (40/21), (-32/105), (8/21), (-1/5), (-2/7);
    (-10/3), (-22/15), (32/15), (-21/20), (-2);
    2, (-8/5), (-6/5), (3/2), (4/5);
    0, (9/5), (-2/5), (-3/4), (3/5);
    (3/7), (6/35), (1/35), (-9/70), (-3/35);
    (-25/21), (62/105), (29/105), (-17/70), (-1/35);
    (25/7), (-34/35), (-29/35), (93/70), (31/35);
    (-30/7), (24/35), (2/7), (-9/70), (-36/35);
    2, (-4/5), (-2/5), (3/5), (-4/5);
    (-15/7), (-51/35), (-33/35), (54/35), (57/35);
    (40/7), (24/35), (-16/35), (-3), (-20/7);
    (-10), (26/5), (16/5), (-99/20), (-14/5);
    6, (-12/5), (-6/5), (18/5), (24/5);
    0, (-8/5), (-8/5), (-2/5), (2/5);
    0, (-4), (-12/5), (63/10), (32/5);
    0, 3, 2, (-9/4), (-3);
    0, 0, (12/7), (-9/14), (-6/7);
    0, (16/5), (12/5), (-9/10), (-6/5);
    0, 0, (6/5), (-63/20), (-6/5);
    0, (-32/5), (-48/5), (63/5), 10;
    0, 4, 6, (-51/4), (-16);
    0, 0, 0, 3, 6]

theorem f410desc3_step : f412raise*f410desc2=f410desc3 := by
  refine natFourSparseRowProduct_matrix_check f412raise f410desc2 f410desc3
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 0) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 1) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 2) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 3) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 4) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 5) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 6) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 7) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 8) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 9) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 10) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 11) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 12) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 13) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 14) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 15) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 16) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 17) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 18) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 19) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 20) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 21) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 22) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 23) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 24) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 25) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 26) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 27) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 28) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 29) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 30) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 31) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 32) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 33) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 34) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 35) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 36) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 37) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f412raiseSparseRows 38) f410desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc3 38 b)
      (by decide +kernel) 0 b

theorem f410desc3_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f410desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f410basis (complexify b410relative *ᵥ x))
    f412basis f413basis f410desc2 f410desc3 f412raise
    f410desc2_actual f412_actual_raise_block f410desc3_step x

#print axioms f410desc2_step
#print axioms f410desc2_actual
#print axioms f410desc3_step
#print axioms f410desc3_actual
end TorusLean.BosonFiniteCertificate
