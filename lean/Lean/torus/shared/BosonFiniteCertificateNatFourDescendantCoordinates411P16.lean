import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates411P15

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

def f411desc5 : Matrix (Fin 64) (Fin 4) ℚ :=
  !![(1/252), (-1/210), (-1/210), (1/120);
    (1/63), (-2/105), (-2/105), (1/30);
    (5/126), (1/105), (4/105), (-2/21);
    (5/63), (-1/15), (1/21), (-31/210);
    (-5/42), (-6/35), (-1/35), (3/28);
    (-11/63), (1/105), (1/105), (7/30);
    (31/126), (23/105), (8/105), (1/105);
    (5/63), (8/105), (-4/105), (-5/42);
    (-5/28), (-3/70), (-1/14), (-13/280);
    (-5/42), (3/35), (2/35), (-1/14);
    (-5/63), (37/105), (19/105), (-31/105);
    (20/63), (-1/15), (-43/105), (64/105);
    (-20/21), (1/5), (-13/35), (4/7);
    (13/63), (61/105), (31/105), (-103/105);
    (15/7), (-12/35), (6/35), (-5/7);
    (-10/7), (-6/7), (2/35), (31/35);
    (20/63), (1/21), (-5/21), (253/420);
    (-10/63), (-8/21), (-4/15), (20/21);
    (-170/63), (22/105), (94/105), (-103/42);
    (25/63), (19/105), (-83/105), (-23/21);
    (5/7), (74/35), (-4/5), (53/35);
    (-10/7), (16/7), (4/7), (18/35);
    (-5/63), (-14/15), (20/21), (-142/105);
    (100/63), (-31/21), (5/21), (-8/21);
    (50/21), (-8/7), (-16/7), (29/7);
    (20/21), (-164/35), (68/35), (-92/35);
    (-25/42), (22/7), (-1/7), (71/28);
    (-100/21), (162/35), (66/35), (-6/7);
    0, (-14/5), (6/5), (-7/2);
    (7/3), 0, (-2), 0;
    (-5/21), 0, (2/35), (-2/35);
    (55/126), (-20/21), (-7/15), (143/210);
    (10/7), 0, (-12/35), (12/35);
    (-5/42), (10/7), (41/35), (-23/14);
    (125/63), (-256/105), (2/15), (2/21);
    (15/14), (-3), (-16/35), (67/70);
    (-10/7), 0, (12/35), (-12/35);
    (20/21), (-8/7), (-12/35), (1/5);
    (-80/63), (116/21), (412/105), (-94/15);
    (-275/63), (2/3), (8/21), (55/21);
    (-15/7), (-201/35), (-29/5), (387/35);
    0, (92/7), (12/7), (-60/7);
    (50/7), 0, (-12/7), (12/7);
    (200/21), (-31/7), (-59/7), 10;
    (-40/21), (-384/35), (-16/5), (-48/35);
    (20/3), (-12), (-12/5), (-8/5);
    (-100/7), (90/7), (54/7), (-90/7);
    (-10/3), (6/5), (2/5), 12;
    6, 0, (-4), 12;
    (-65/21), (8/7), (6/7), (-113/70);
    (-400/63), (4/21), (-32/21), (71/21);
    (-50/7), (-27/7), (3/7), (153/28);
    (-40/7), (60/7), (52/7), (-198/35);
    5, 8, (14/5), (-33/10);
    (425/21), (-90/7), (-64/7), (72/7);
    (-100/7), (124/7), 28, (-352/7);
    (40/3), (-28), (-76/5), (152/5);
    (-25), 26, 24, (-50);
    15, (-18/5), (-16/5), (-12);
    (200/21), 0, (-16/7), (16/7);
    (-50/3), 8, (-12), 32;
    10, (-128/5), (-28), (268/5);
    0, 4, 8, (-14);
    0, 5, 10, (-35/2)]

theorem f411desc5_step : f415raise*f411desc4=f411desc5 := by
  refine natFourSparseRowProduct_matrix_check f415raise f411desc4 f411desc5
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 0) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 1) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 2) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 3) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 4) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 5) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 6) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 7) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 8) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 9) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 10) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 11) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 12) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 13) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 14) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 15) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 16) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 17) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 18) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 19) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 20) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 21) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 22) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 23) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 24) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 25) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 26) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 27) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 28) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 29) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 30) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 31) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 32) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 33) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 34) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 35) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 36) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 37) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 38) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 39) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 40) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 41) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 42) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 43) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 44) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 45) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 46) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 47) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 48) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 49) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 50) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 51) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 52) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 53) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 54) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 55) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 56) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 57) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 58) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 59) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 60) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 61) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 62) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f415raiseSparseRows 63) f411desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc5 63 b)
      (by decide +kernel) 0 b

theorem f411desc5_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f411basis (complexify b411relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f411desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f411basis (complexify b411relative *ᵥ x))
    f415basis f416basis f411desc4 f411desc5 f415raise
    f411desc4_actual f415_actual_raise_block f411desc5_step x

#print axioms f411desc5_step
#print axioms f411desc5_actual
end TorusLean.BosonFiniteCertificate
