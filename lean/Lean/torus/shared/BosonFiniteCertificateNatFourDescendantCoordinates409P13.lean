import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409P11

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

def f409desc3 : Matrix (Fin 34) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    0, 0, 0;
    (-1/35), (-9/140), (-23/140);
    (-4/35), (27/140), (-1/140);
    (19/70), (9/56), (9/56);
    (4/35), (-27/140), (1/140);
    (-1/5), (-3/20), (-1/20);
    (2/7), (-9/35), (-11/70);
    (-8/35), (-9/140), (47/140);
    (-4/7), (9/140), (93/140);
    (36/35), (-117/140), (-89/140);
    (-4/5), (27/20), (-1/20);
    (3/35), (27/140), (69/140);
    (8/7), (-9/70), (-93/70);
    (4/5), (-9/5), (-3/5);
    0, (-27/20), (21/20);
    (-8/5), (27/10), (-1/10);
    (-4/5), (9/20), (13/20);
    1, (-3/4), (-3/4);
    0, (3/10), (1/10);
    (-6/5), (27/20), (9/20);
    (-32/35), (-72/35), (-44/35);
    0, (9/20), (-7/20);
    0, (27/10), (9/10);
    (96/35), (-27/14), (-27/14);
    (-8/5), (-9/10), (27/10);
    (12/5), (-81/20), (3/20);
    (-32/5), (36/5), (32/5);
    4, (-9/4), (-13/4);
    (12/5), 0, 0;
    (-24/5), (27/5), (9/5);
    3, (-27/4), (-33/4);
    0, 0, 0;
    0, 1, 3]

theorem f409desc3_step : f411raise*f409desc2=f409desc3 := by
  refine natFourSparseRowProduct_matrix_check f411raise f409desc2 f409desc3
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 0) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 1) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 2) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 3) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 4) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 5) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 6) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 7) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 8) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 9) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 10) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 11) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 12) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 13) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 14) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 15) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 16) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 17) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 18) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 19) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 20) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 21) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 22) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 23) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 24) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 25) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 26) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 27) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 28) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 29) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 30) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 31) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 32) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f411raiseSparseRows 33) f409desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc3 33 b)
      (by decide +kernel) 0 b

theorem f409desc3_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f409desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f409basis (complexify b409relative *ᵥ x))
    f411basis f412basis f409desc2 f409desc3 f411raise
    f409desc2_actual f411_actual_raise_block f409desc3_step x

def f409desc4 : Matrix (Fin 39) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (-3/70), (3/56), (3/56);
    (-1/35), (-9/140), (-23/140);
    (-1/7), (9/70), (-6/35);
    (11/70), (99/280), (43/280);
    (27/70), (-9/280), (47/280);
    (-2/7), (-69/140), (-13/140);
    (2/7), (-9/35), (-11/70);
    (2/7), (-99/140), (-43/140);
    (-36/35), (27/70), (69/70);
    1, (-9/20), (7/20);
    (16/35), (9/70), (-47/70);
    (-6/5), (21/20), (-3/20);
    (-1/7), (9/70), (29/35);
    (26/35), (9/28), (9/28);
    (104/35), (-387/140), (-359/140);
    0, (-63/20), (29/20);
    (-16/35), (18/7), (-10/7);
    (-16/5), (81/20), (-3/20);
    (-4/5), (-9/10), (17/10);
    (11/5), (-9/5), (-8/5);
    (2/7), (3/70), (-2/35);
    (-10/7), (153/70), (38/35);
    (-94/35), (-9/14), (-1/7);
    (4/35), (-171/70), (-157/70);
    (-4/5), (36/5), (7/5);
    (3/7), (27/28), (-15/28);
    (16/5), (-9), (-5);
    (8/5), (-117/20), (31/20);
    (12/5), 0, 3;
    (-48/5), 9, 9;
    (-16/5), (63/10), (71/10);
    5, (-3), (-4);
    (36/7), (-27/14), (-27/14);
    (4/5), (9/2), (9/2);
    (18/5), (-243/20), (-291/20);
    (-16), 18, 10;
    10, (-63/4), (-79/4);
    0, 4, 12]

theorem f409desc4_step : f412raise*f409desc3=f409desc4 := by
  refine natFourSparseRowProduct_matrix_check f412raise f409desc3 f409desc4
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 0) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 1) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 2) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 3) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 4) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 5) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 6) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 7) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 8) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 9) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 10) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 11) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 12) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 13) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 14) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 15) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 16) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 17) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 18) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 19) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 20) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 21) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 22) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 23) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 24) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 25) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 26) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 27) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 28) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 29) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 30) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 31) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 32) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 33) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 34) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 35) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 36) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 37) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f412raiseSparseRows 38) f409desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc4 38 b)
      (by decide +kernel) 0 b

theorem f409desc4_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f409desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f409basis (complexify b409relative *ᵥ x))
    f412basis f413basis f409desc3 f409desc4 f412raise
    f409desc3_actual f412_actual_raise_block f409desc4_step x

#print axioms f409desc3_step
#print axioms f409desc3_actual
#print axioms f409desc4_step
#print axioms f409desc4_actual
end TorusLean.BosonFiniteCertificate
