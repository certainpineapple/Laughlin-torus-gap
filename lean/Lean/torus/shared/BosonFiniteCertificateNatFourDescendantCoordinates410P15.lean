import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates410P14

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

def f410desc5 : Matrix (Fin 54) (Fin 5) ℚ :=
  !![(-1/126), (1/126), (1/126), (-1/84), (-1/84);
    (-5/126), (5/126), (5/126), (-5/84), (-5/84);
    (-25/126), (-1/630), (-19/630), (37/420), (7/60);
    (-5/18), (7/90), (-41/630), (17/105), (107/420);
    (25/126), (127/630), (-53/630), (-2/21), (-5/84);
    (-1/126), (1/126), (-5/18), (-13/84), (-31/84);
    (-65/126), (-53/630), (-143/630), (13/84), (-17/84);
    (5/14), (17/70), (3/14), (9/28), (1/20);
    (20/63), (-37/315), (-4/45), (19/210), (13/210);
    (-5/21), (-59/105), (-1/3), (17/28), (37/70);
    (40/63), (52/315), (232/315), (-59/105), (-8/15);
    (235/63), (-41/315), (319/315), (-13/12), (-41/42);
    (-20/7), (-54/35), (-4/35), (3/7), 1;
    (-15/7), (-23/35), (9/35), (-5/14), (93/70);
    (20/7), (12/35), (4/7), (-1), (6/35);
    (-65/21), (-11/105), (5/21), (-59/140), (-5/7);
    (-130/63), (146/315), (22/63), (-61/42), (-214/105);
    (25/21), (17/21), (-19/21), (47/28), (37/14);
    (-75/7), (19/7), (-11/35), (99/70), (227/70);
    (40/7), (108/35), (-8/7), (-82/35), (-74/35);
    (400/63), (-22/63), (-16/9), (55/42), (26/21);
    (25/7), (3/7), (11/7), (10/7), (25/14);
    (-40/7), (-16/7), (96/35), (-2/35), (-136/35);
    (20/3), (-58/15), (-28/15), (17/10), (-11/5);
    (-50/7), (1/7), (38/7), (-25/7), (-27/7);
    0, (2/5), (-8/5), (-3/2), 0;
    2, 2, (-2), 0, 2;
    (10/9), (-1/9), (-62/315), (13/105), (23/210);
    (20/21), (22/21), (44/105), (-31/35), (-23/35);
    (320/63), (58/63), (416/315), (-103/105), (-103/105);
    (100/21), (-37/21), (-4/21), (17/7), (19/14);
    (-10), (-9/5), (-18/35), (171/70), (39/70);
    (40/7), (-12/7), (-16/35), (-4/5), (-114/35);
    (-215/21), (47/21), (23/21), (-221/140), (-31/35);
    (200/21), (-116/21), (-152/21), (52/7), (50/7);
    (-75/7), (33/7), (-17/7), (3/28), (-1/2);
    (-160/7), (352/35), (24/7), (-24/5), (-216/35);
    20, (-2), (-12/5), (33/10), (7/5);
    (500/21), (-122/21), (-164/21), (17/14), (12/7);
    (-400/21), (64/21), (88/21), (-18), (-92/7);
    (40/3), (-368/15), (-176/15), 28, (148/5);
    (-50/3), (11/3), (14/3), (-7/2), (-1);
    10, (38/5), (-2/5), 9, 10;
    (-25/3), (-5/3), (1/3), (7/4), 2;
    (75/7), (-33/7), (29/7), (3/4), (-6/7);
    (-150/7), (150/7), 18, (-327/14), (-136/7);
    10, (14/5), 6, (-9/2), (32/5);
    (400/21), (104/21), (128/21), (-34/7), (-8);
    (-100/3), (4/3), (-20/3), 2, 0;
    20, (-108/5), (-12), 12, (56/5);
    0, 19, 20, (-93/2), (-67);
    0, (-8), (-16), 26, 24;
    0, (-20), (-24), 39, 44;
    0, 15, 20, (-45/2), (-15)]

theorem f410desc5_step : f414raise*f410desc4=f410desc5 := by
  refine natFourSparseRowProduct_matrix_check f414raise f410desc4 f410desc5
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 0) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 1) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 2) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 3) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 4) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 5) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 6) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 7) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 8) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 9) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 10) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 11) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 12) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 13) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 14) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 15) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 16) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 17) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 18) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 19) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 20) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 21) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 22) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 23) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 24) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 25) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 26) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 27) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 28) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 29) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 30) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 31) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 32) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 33) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 34) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 35) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 36) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 37) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 38) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 39) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 40) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 41) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 42) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 43) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 44) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 45) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 46) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 47) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 48) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 49) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 50) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 51) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 52) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f414raiseSparseRows 53) f410desc4 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc5 53 b)
      (by decide +kernel) 0 b

theorem f410desc5_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f410desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f410basis (complexify b410relative *ᵥ x))
    f414basis f415basis f410desc4 f410desc5 f414raise
    f410desc4_actual f414_actual_raise_block f410desc5_step x

#print axioms f410desc5_step
#print axioms f410desc5_actual
end TorusLean.BosonFiniteCertificate
