import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates410P13

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

def f410desc4 : Matrix (Fin 47) (Fin 5) ℚ :=
  !![(-1/126), (1/126), (1/126), (-1/84), (-1/84);
    (-1/63), (1/63), (1/63), (-1/42), (-1/42);
    (-23/126), (-11/630), (-29/630), (47/420), (59/420);
    (-2/21), (2/21), (-2/105), (1/20), (4/35);
    (37/126), (67/630), (-41/630), (-61/420), (-73/420);
    (-19/63), (-31/315), (-67/315), (-1/105), (-41/210);
    (-3/14), (1/70), (-1/70), (23/140), (-1/140);
    (2/7), (4/35), (4/35), (11/140), (1/35);
    (22/63), (-47/315), (-38/315), (29/210), (23/210);
    (-4/7), (-8/35), 0, (3/28), (1/35);
    (88/63), (64/315), (244/315), (-323/420), (-83/105);
    (110/63), (-172/315), (116/315), (-1/42), (17/105);
    (-4), (-4/5), (-2/35), (33/70), (43/35);
    (16/7), (4/35), (12/35), (-81/70), (4/35);
    (-53/21), (13/105), (5/21), (-37/70), (-26/35);
    (100/63), (4/315), (-284/315), (157/420), (5/21);
    (-15/7), (47/35), (-13/35), (93/70), (157/70);
    (-32/7), (76/35), (4/35), (-27/70), (-8/35);
    4, (2/5), (-4/5), (-2/5), (-1);
    (100/21), (-38/105), (-92/105), (131/140), 1;
    (-80/21), (-4/21), (388/105), (-62/35), (-86/35);
    (8/3), (-64/15), (-16/15), (21/10), (-6/5);
    (-10/3), (1/3), (26/15), (-9/5), (-7/5);
    2, 2, (-2), 0, 2;
    (16/21), (4/105), (-8/105), (-1/70), 0;
    (-16/21), (122/105), (68/105), (-19/20), (-24/35);
    (40/9), (-4/9), (-32/315), (31/42), (52/105);
    (-10/7), (-27/35), (-16/35), (12/7), (7/10);
    (-32/7), (-8/35), 0, (9/35), (-48/35);
    4, (-4/5), (-2/5), (1/20), (-1);
    (-130/21), (-22/105), (-46/105), (17/20), (43/35);
    (80/7), (-148/35), (-184/35), (543/140), (121/35);
    (-120/7), (64/7), (144/35), (-597/70), (-38/5);
    8, (-4/5), (-4/5), (18/5), (22/5);
    (160/21), (-128/105), (-176/105), (-18/5), (-96/35);
    (-40/3), (-52/15), (-4/15), (-1/2), (12/5);
    8, (-8), (-24/5), (57/5), 12;
    0, (34/5), (16/5), (-6/5), (-2);
    (-15/7), (-51/35), (27/35), (9/10), (27/35);
    (40/7), (136/35), (248/35), (-204/35), (-232/35);
    (-10), (42/5), (34/5), (-9), (-26/5);
    6, (-12/5), 0, (9/20), (18/5);
    0, (-8/5), (-32/5), (52/5), 8;
    0, (-44/5), (-36/5), (-3/10), (-8);
    0, 7, 8, (-15), (-19);
    0, (-32/5), (-48/5), (78/5), 16;
    0, 4, 6, (-15/4), 2]

theorem f410desc4_step : f413raise*f410desc3=f410desc4 := by
  refine natFourSparseRowProduct_matrix_check f413raise f410desc3 f410desc4
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 0) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 1) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 2) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 3) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 4) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 5) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 6) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 7) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 8) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 9) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 10) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 11) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 12) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 13) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 14) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 15) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 16) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 17) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 18) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 19) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 20) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 21) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 22) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 23) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 24) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 25) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 26) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 27) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 28) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 29) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 30) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 31) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 32) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 33) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 34) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 35) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 36) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 37) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 38) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 39) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 40) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 41) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 42) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 43) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 44) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 45) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 46) f410desc3 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc4 46 b)
      (by decide +kernel) 0 b

theorem f410desc4_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f410desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f410basis (complexify b410relative *ᵥ x))
    f413basis f414basis f410desc3 f410desc4 f413raise
    f410desc3_actual f413_actual_raise_block f410desc4_step x

#print axioms f410desc4_step
#print axioms f410desc4_actual
end TorusLean.BosonFiniteCertificate
