import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406P11

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

def f406desc6 : Matrix (Fin 34) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-6/5), (6/5), (6/5);
    (-12/5), (7/5), (16/15);
    (-4), 0, (-2);
    (-9/2), (1/2), (-29/6);
    (-6/5), (26/5), (-52/15);
    (4/5), (21/5), (-4/5);
    (-9/5), (14/5), (47/15);
    0, (-2), (-2/3);
    (-6), (-14), (-44/3);
    (-6), (-6), (-8);
    18, 14, (44/3);
    0, (-9), (-4);
    (-36), (-12), 8;
    (-24), 12, 40;
    (36/5), (54/5), (134/5);
    (-32), 12, 20;
    18, 34, (40/3);
    15, 5, (-25/3);
    6, 0, (2/3);
    45, (-12), (-11);
    24, (-16), (-40/3);
    24, (-26), (-2/3);
    (126/5), (-96/5), (14/5);
    36, 12, 0;
    (-84), 60, 32;
    18, (-90), (-52);
    (-24), (-16), (-184/3);
    90, (-110), (-500/3);
    (-36), 52, 28;
    (-144), 120, 80;
    0, (-15), 0;
    60, 0, 60;
    20, 0, 20]

theorem f406desc6_step : f411raise*f406desc5=f406desc6 := by
  refine natFourSparseRowProduct_matrix_check f411raise f406desc5 f406desc6
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 0) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 1) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 2) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 3) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 4) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 5) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 6) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 7) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 8) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 9) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 10) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 11) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 12) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 13) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 14) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 15) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 16) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 17) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 18) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 19) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 20) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 21) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 22) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 23) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 24) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 25) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 26) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 27) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 28) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 29) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 30) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 31) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 32) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 33) f406desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc6 33 b)
      (by decide +kernel) 0 b

theorem f406desc6_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f406desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f411basis f412basis f406desc5 f406desc6 f411raise
    f406desc5_actual f411_actual_raise_block f406desc6_step x

def f406desc7 : Matrix (Fin 39) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-3/2), (3/2), (3/2);
    (-18/5), (13/5), (34/15);
    (-32/5), (7/5), (-14/15);
    (-17/2), (1/2), (-41/6);
    (-57/10), (57/10), (-83/10);
    (2/5), (68/5), (-76/15);
    (-21/5), (26/5), (83/15);
    (-42/5), (32/5), (116/15);
    (-14), (-16), (-58/3);
    (-21), (-19), (-97/3);
    (48/5), (92/5), (-4/15);
    (98/5), (112/5), (196/15);
    0, (-11), (-14/3);
    (-42), (-44), (-44/3);
    (-66), (-6), 40;
    (42/5), (238/5), (1624/15);
    (-68), 0, 28;
    (-70), 70, (280/3);
    (126/5), (224/5), (602/15);
    63, 49, (-35/3);
    (21/5), (14/5), (19/5);
    63, (-14), (-29/3);
    63, (-42), (-39);
    42, (-48), (-22);
    (462/5), (-252/5), (98/5);
    126, (-21), (-26);
    0, 40, (40/3);
    (-42), (-70), (56/3);
    (378/5), (-588/5), (-98/5);
    (-140), 56, (-28/3);
    168, (-308), (-1484/3);
    105, (-105), (-175);
    0, 64, 28;
    (-336), 336, 196;
    (-126), 0, 28;
    (-252), 224, (476/3);
    210, (-140), (-140/3);
    140, 0, 140]

theorem f406desc7_step : f412raise*f406desc6=f406desc7 := by
  refine natFourSparseRowProduct_matrix_check f412raise f406desc6 f406desc7
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 0) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 1) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 2) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 3) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 4) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 5) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 6) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 7) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 8) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 9) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 10) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 11) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 12) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 13) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 14) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 15) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 16) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 17) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 18) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 19) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 20) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 21) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 22) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 23) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 24) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 25) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 26) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 27) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 28) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 29) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 30) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 31) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 32) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 33) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 34) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 35) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 36) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 37) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 38) f406desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc7 38 b)
      (by decide +kernel) 0 b

theorem f406desc7_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f406desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f412basis f413basis f406desc6 f406desc7 f412raise
    f406desc6_actual f412_actual_raise_block f406desc7_step x

#print axioms f406desc6_step
#print axioms f406desc6_actual
#print axioms f406desc7_step
#print axioms f406desc7_actual
end TorusLean.BosonFiniteCertificate
