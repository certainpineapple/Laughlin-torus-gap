import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates413P14

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

def f413desc2 : Matrix (Fin 54) (Fin 5) ℚ :=
  !![(-1/924), (1/792), (1/792), (-1/495), (-1/495);
    (1/132), (-7/792), (-7/792), (7/495), (7/495);
    (-31/924), (85/5544), (41/5544), (-19/3465), (2/495);
    (59/924), (7/792), (5/5544), (-82/3465), (-197/6930);
    (-1/44), (-61/1848), (-139/5544), (13/385), (23/2310);
    (-3/28), (1/56), (13/504), (1/105), (1/70);
    (17/84), (1/72), (1/72), (-1/45), (-1/126);
    (-3/28), (-1/56), (-1/56), 0, 0;
    (1/42), (-1/252), (1/252), (-4/315), (-1/45);
    (-17/154), (-1/462), (85/1386), (-73/1155), (-223/2310);
    (4/21), (-8/63), (-4/63), (52/315), (64/315);
    (-11/42), (41/252), (25/252), (-52/315), (-1/315);
    (1/21), (-1/126), (-11/126), (-44/315), (-10/63);
    (5/14), (-1/7), (-1/7), (1/5), (1/14);
    (-2/7), (1/7), (1/7), 0, 0;
    (9/77), (17/924), (-367/2772), (8/77), (59/462);
    (-4/21), (17/63), (10/63), (-2/9), (-46/315);
    (25/42), (-85/252), (5/36), (26/315), (-82/315);
    (-9/14), (-1/14), (-3/14), (3/7), (5/14);
    (2/7), (-1/7), (1/7), (-16/35), (-4/35);
    (-10/21), (-5/18), (5/126), (8/315), (-7/45);
    (15/14), (5/28), (-15/28), (12/35), (22/35);
    (-12/7), (13/7), (11/21), (-4/5), (-2/5);
    1, (-2/3), (-1/3), (2/3), (1/15);
    0, (-5/14), (5/14), (-19/35), (-2/7);
    0, (-3/2), (-1/6), (4/5), (1/5);
    0, 1, 0, (-2/5), 0;
    (-1/42), (19/252), (5/252), (-2/45), (-2/315);
    (3/77), (-109/462), (-31/198), (116/385), (304/1155);
    (-1/3), (19/126), (5/126), (-4/45), (-94/315);
    (25/42), (65/252), (-5/252), (-4/45), (-58/315);
    (-9/14), (-13/28), (1/28), (2/5), (3/7);
    (2/7), (2/7), 0, (-12/35), (-6/35);
    (3/7), (-5/84), (55/252), (-2/5), (-13/30);
    (-10/7), (10/21), (20/63), (-76/105), (-2/15);
    (45/14), (-10/7), (-20/21), (11/7), (131/70);
    (-36/7), (11/7), (41/21), (-68/35), (-66/35);
    3, (-1), (-4/3), (6/5), (3/5);
    0, (-25/42), (-25/42), (16/15), (127/105);
    0, (55/21), (5/3), (-52/21), (-374/105);
    0, (-1/3), (-1/3), (-4/15), (26/15);
    0, (-10/3), (-5/3), (53/15), (23/15);
    0, 2, 1, (-2), (-6/5);
    0, (5/12), (5/36), 0, (1/30);
    0, (-5/4), (-115/84), (72/35), (3/2);
    0, (15/14), (5/14), (-20/7), (-97/35);
    0, (-1/2), (-1/6), (12/5), (7/5);
    0, (20/21), (20/7), (-376/105), (-80/21);
    0, (-5/3), (-5), (88/15), (142/15);
    0, 1, 3, (-24/5), (-22/5);
    0, 0, 0, 1, (-1/5);
    0, 0, 0, (8/5), (8/5);
    0, 0, 0, (-12/5), (-28/5);
    0, 0, 0, 1, 3]

theorem f413desc2_step : f414raise*f413desc1=f413desc2 := by
  refine natFourSparseRowProduct_matrix_check f414raise f413desc1 f413desc2
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 0) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 1) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 2) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 3) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 4) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 5) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 6) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 7) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 8) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 9) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 10) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 11) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 12) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 13) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 14) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 15) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 16) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 17) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 18) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 19) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 20) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 21) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 22) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 23) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 24) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 25) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 26) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 27) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 28) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 29) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 30) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 31) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 32) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 33) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 34) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 35) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 36) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 37) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 38) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 39) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 40) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 41) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 42) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 43) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 44) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 45) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 46) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 47) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 48) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 49) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 50) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 51) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 52) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 53) f413desc1 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc2 53 b)
      (by decide +kernel) 0 b

theorem f413desc2_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f413basis (complexify b413relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f413desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f413basis (complexify b413relative *ᵥ x))
    f414basis f415basis f413desc1 f413desc2 f414raise
    f413desc1_actual f414_actual_raise_block f413desc2_step x

#print axioms f413desc2_step
#print axioms f413desc2_actual
end TorusLean.BosonFiniteCertificate
