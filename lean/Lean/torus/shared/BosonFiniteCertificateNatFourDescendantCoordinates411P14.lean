import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates411P13

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

def f411desc3 : Matrix (Fin 47) (Fin 4) ℚ :=
  !![(1/252), (-1/210), (-1/210), (1/120);
    (-1/126), (1/105), (1/105), (-1/60);
    (11/252), (1/210), (1/30), (-73/840);
    0, (-3/35), (-1/35), (3/70);
    (-41/252), (-1/210), (-1/210), (13/120);
    (19/126), (11/105), (1/21), (-11/420);
    (3/28), (1/70), (-1/70), (-13/280);
    (-1/7), (-1/35), (-1/35), 0;
    (-1/9), (8/105), (1/21), (-23/420);
    (5/21), (-1/35), (-1/5), (13/35);
    (-1/9), (17/105), (-13/105), (16/105);
    (-20/63), (4/15), (22/105), (-149/210);
    1, (-18/35), (-6/35), (-3/70);
    (-4/7), (-2/35), (6/35), (13/35);
    (-1/42), (-2/35), 0, (1/7);
    (-5/9), (-23/105), (67/105), (-118/105);
    (-5/14), (-3/35), (-19/35), (57/140);
    0, (6/7), (-18/35), (27/35);
    0, (4/5), (2/5), (-1/2);
    (25/21), (-19/35), (-1/5), (16/35);
    (-10/21), (44/35), 0, (37/35);
    (2/3), (-18/5), (2/5), (-6/5);
    (-5/3), (9/5), (4/5), (-9/10);
    1, 0, (-4/5), (3/5);
    0, (-6/35), (-2/35), (3/35);
    (3/7), (-9/35), (-1/35), (-9/70);
    (20/63), (14/15), (62/105), (-83/105);
    0, (-36/35), (-1/7), (27/28);
    0, (-36/35), (-12/35), (18/35);
    0, (3/5), (1/5), (-4/5);
    (-10/7), (39/35), (5/7), (-6/5);
    (15/7), (-33/35), (-71/35), (129/35);
    (-30/7), (18/35), (2/5), (18/35);
    2, (12/5), 0, (-9/5);
    (80/21), (-24/35), (-8/7), (-12/35);
    (-20/3), 2, (18/5), (-37/5);
    4, (-36/5), (-4), (36/5);
    0, (18/5), (4/5), (9/5);
    (-15/14), (-18/35), (-18/35), (9/10);
    (20/7), (-72/35), (8/35), (-24/35);
    (-5), (24/5), (28/5), (-33/5);
    3, (-9/5), (-9/5), (9/2);
    0, (16/5), (8/5), (-16/5);
    0, (-6), (-6), (33/5);
    0, 3, 4, (-21/2);
    0, (-8/5), (-24/5), (52/5);
    0, 1, 3, (-7/2)]

theorem f411desc3_step : f413raise*f411desc2=f411desc3 := by
  refine natFourSparseRowProduct_matrix_check f413raise f411desc2 f411desc3
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 0) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 1) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 2) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 3) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 4) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 5) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 6) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 7) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 8) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 9) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 10) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 11) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 12) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 13) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 14) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 15) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 16) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 17) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 18) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 19) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 20) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 21) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 22) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 23) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 24) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 25) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 26) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 27) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 28) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 29) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 30) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 31) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 32) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 33) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 34) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 35) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 36) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 37) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 38) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 39) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 40) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 41) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 42) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 43) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 44) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 45) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 46) f411desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc3 46 b)
      (by decide +kernel) 0 b

theorem f411desc3_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f411basis (complexify b411relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f411desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f411basis (complexify b411relative *ᵥ x))
    f413basis f414basis f411desc2 f411desc3 f413raise
    f411desc2_actual f413_actual_raise_block f411desc3_step x

#print axioms f411desc3_step
#print axioms f411desc3_actual
end TorusLean.BosonFiniteCertificate
