import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates413P15

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

def f413desc3 : Matrix (Fin 64) (Fin 5) ℚ :=
  !![(-1/924), (1/792), (1/792), (-1/495), (-1/495);
    (1/231), (-1/198), (-1/198), (4/495), (4/495);
    (-2/77), (1/154), (-1/693), (2/231), (1/55);
    (1/33), (67/2772), (23/2772), (-101/3465), (-169/6930);
    (19/462), (-67/2772), (-67/2772), (1/99), (-64/3465);
    (-10/77), (-1/66), (1/1386), (10/231), (4/165);
    (2/21), (2/63), (5/126), (-4/315), (2/315);
    (2/21), (-1/252), (-1/252), (-1/45), (-1/126);
    (-3/28), (-1/56), (-1/56), 0, 0;
    (3/77), (-5/231), (-19/1386), (6/385), (1/165);
    (-10/77), (19/924), (233/2772), (-23/231), (-307/2310);
    (16/77), (-103/924), (-1/2772), (3/55), (23/462);
    (-9/77), (-1/33), (-10/693), (26/385), (254/1155);
    (-3/7), (4/21), (4/63), (-2/7), (-2/15);
    (17/21), (-31/252), (-17/84), (1/63), (-13/126);
    (-3/7), (3/28), (3/28), (1/5), (1/14);
    (1/154), (5/308), (-197/2772), (47/1155), (12/385);
    (18/77), (83/462), (-235/1386), (58/385), (361/1155);
    (1/7), (2/21), (25/63), (-32/105), (-43/105);
    0, (-5/12), (-41/252), (13/35), (-13/210);
    0, (-5/14), (-3/14), (6/35), (11/35);
    0, 0, (2/7), (-16/35), (-4/35);
    (-2/3), (-1/126), (25/126), (-62/315), (-19/63);
    (5/7), (-5/7), (-20/63), (10/21), (2/35);
    (-9/7), (55/28), (-19/84), (-1/35), (41/70);
    (4/7), (8/21), 0, (8/105), (-8/21);
    (15/14), (-5/28), (-5/28), (-1/5), (12/35);
    (-12/7), (-5/14), (15/14), (-38/35), (-27/35);
    1, (-13/6), (-1/2), (22/15), (4/15);
    0, (3/2), (-1/6), (-2/5), (1/5);
    0, (1/14), (1/42), (-2/35), (-1/35);
    (-1/7), (-1/84), (-1/28), (11/105), (31/210);
    (-8/77), (-7/33), (-125/693), (436/1155), (194/1155);
    0, (4/7), (5/42), (-12/35), (-17/35);
    0, (-3/14), (-1/14), (6/35), (3/35);
    0, (-9/28), (-3/28), (9/35), (23/70);
    0, (3/7), (1/7), (-12/35), (-6/35);
    (48/77), (-79/154), (-5/22), (118/385), (17/77);
    (-10/7), (13/14), (125/126), (-202/105), (-61/35);
    (25/7), (-65/84), (-15/28), (79/105), (233/210);
    (-27/7), (-6/7), (6/7), (6/7), (6/5);
    (12/7), 0, (-4/7), (-24/35), (-8/7);
    (-40/21), (-25/63), (-5/21), (116/315), (58/63);
    (30/7), (5/28), (-85/84), (11/7), (19/14);
    (-48/7), (40/7), (80/21), (-192/35), (-144/35);
    4, (-2), (-2), (8/5), (12/5);
    0, (-15/14), (5/14), (18/35), (-81/35);
    0, (-9/2), (-11/6), (18/5), (13/5);
    0, 3, 1, (-12/5), (-6/5);
    (3/7), (5/14), (5/14), (-2/5), (-2/5);
    (-10/7), (10/21), (-40/63), (4/3), (22/15);
    (45/14), (-45/28), (-55/28), (27/35), (3/5);
    (-36/7), (15/7), (15/7), (-12/5), (-114/35);
    3, (-3/2), (-3/2), (18/5), 2;
    0, (-15/7), (-10/21), (8/5), (2/5);
    0, 5, (65/21), (-332/35), (-254/35);
    0, (-1), (1/3), (4/5), (26/5);
    0, (-5), (-20/3), (52/5), (54/5);
    0, 3, 4, (-24/5), (-6);
    0, (20/21), (20/7), (-208/105), (-232/105);
    0, (-5/3), (-5), (124/15), (26/3);
    0, 1, 3, (-36/5), (-10);
    0, 0, 0, (-4/5), (-12/5);
    0, 0, 0, 1, 3]

theorem f413desc3_step : f415raise*f413desc2=f413desc3 := by
  refine natFourSparseRowProduct_matrix_check f415raise f413desc2 f413desc3
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 0) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 1) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 2) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 3) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 4) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 5) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 6) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 7) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 8) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 9) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 10) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 11) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 12) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 13) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 14) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 15) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 16) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 17) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 18) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 19) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 20) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 21) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 22) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 23) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 24) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 25) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 26) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 27) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 28) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 29) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 30) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 31) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 32) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 33) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 34) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 35) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 36) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 37) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 38) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 39) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 40) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 41) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 42) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 43) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 44) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 45) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 46) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 47) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 48) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 49) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 50) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 51) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 52) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 53) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 54) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 55) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 56) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 57) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 58) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 59) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 60) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 61) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 62) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 63) f413desc2 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc3 63 b)
      (by decide +kernel) 0 b

theorem f413desc3_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f413basis (complexify b413relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f413desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f413basis (complexify b413relative *ᵥ x))
    f415basis f416basis f413desc2 f413desc3 f415raise
    f413desc2_actual f415_actual_raise_block f413desc3_step x

#print axioms f413desc3_step
#print axioms f413desc3_actual
end TorusLean.BosonFiniteCertificate
