import torus.shared.BosonFiniteCertificateNatFourRaiseSparse407
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse408
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse409
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406P07

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

def f406desc2 : Matrix (Fin 15) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    0, 0, 0;
    (-3/5), (-2/5), (-11/15);
    (-2/5), (2/5), (-4/15);
    (1/2), (1/2), (1/6);
    (9/5), (-4/5), (-7/15);
    (-12/5), (2/5), (26/15);
    2, (-2), (4/3);
    (-3), 2, (5/3);
    2, 0, (-2);
    (6/5), (4/5), (2/15);
    (-3), 2, (-1/3);
    2, (-4), (-10/3);
    0, 0, 0;
    0, 1, 2]

theorem f406desc2_step : f407raise*f406desc1=f406desc2 := by
  refine natFourSparseRowProduct_matrix_check f407raise f406desc1 f406desc2
    f407raiseSparseRows f407_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 0) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 1) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 2) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 3) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 4) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 5) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 6) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 7) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 8) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 9) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 10) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 11) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 12) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 13) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f407raiseSparseRows 14) f406desc1 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc2 14 b)
      (by decide +kernel) 0 b

theorem f406desc2_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f406desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f407basis f408basis f406desc1 f406desc2 f407raise
    f406desc1_actual f407_actual_raise_block f406desc2_step x

def f406desc3 : Matrix (Fin 18) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-3/10), (3/10), (3/10);
    (-3/5), (-2/5), (-11/15);
    (-1), 0, (-1);
    (3/5), (7/5), (1/15);
    (9/5), (-4/5), (-7/15);
    0, (-2), (-2/3);
    (-6/5), (-4/5), (38/15);
    3, (-1), (5/3);
    (-27/5), (12/5), (17/5);
    0, 2, (2/3);
    2, 0, (-2);
    3, 0, (-1/3);
    (-9/5), (24/5), (9/5);
    3, (-8), (-17/3);
    (-9), 6, 1;
    6, (-8), (-26/3);
    0, 4, 8]

theorem f406desc3_step : f408raise*f406desc2=f406desc3 := by
  refine natFourSparseRowProduct_matrix_check f408raise f406desc2 f406desc3
    f408raiseSparseRows f408_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 0) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 1) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 2) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 3) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 4) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 5) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 6) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 7) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 8) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 9) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 10) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 11) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 12) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 13) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 14) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 15) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 16) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f408raiseSparseRows 17) f406desc2 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc3 17 b)
      (by decide +kernel) 0 b

theorem f406desc3_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f406desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f408basis f409basis f406desc2 f406desc3 f408raise
    f406desc2_actual f408_actual_raise_block f406desc3_step x

def f406desc4 : Matrix (Fin 23) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-3/5), (3/5), (3/5);
    (-9/10), (-1/10), (-13/30);
    (-8/5), (-2/5), (-26/15);
    (-2/5), (7/5), (-14/15);
    (3/5), (7/5), (1/15);
    (6/5), (-1/5), (2/15);
    (12/5), (-22/5), (-46/15);
    (-16/5), (-14/5), (-2/15);
    6, 0, 6;
    (-27/5), (2/5), (41/15);
    (-12), 6, 10;
    3, 1, (7/3);
    6, 2, (-16/3);
    (24/5), (-4/5), (-4/5);
    (36/5), (14/5), (2/15);
    0, (-4), (-4/3);
    6, (-9), (-4);
    (-18), 18, 8;
    0, (-18), (-26);
    8, (-8), (-32/3);
    (-9), 10, 9;
    6, 4, (46/3)]

theorem f406desc4_step : f409raise*f406desc3=f406desc4 := by
  refine natFourSparseRowProduct_matrix_check f409raise f406desc3 f406desc4
    f409raiseSparseRows f409_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 0) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 1) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 2) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 3) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 4) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 5) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 6) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 7) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 8) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 9) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 10) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 11) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 12) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 13) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 14) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 15) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 16) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 17) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 18) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 19) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 20) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 21) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f409raiseSparseRows 22) f406desc3 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc4 22 b)
      (by decide +kernel) 0 b

theorem f406desc4_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f406desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f409basis f410basis f406desc3 f406desc4 f409raise
    f406desc3_actual f409_actual_raise_block f406desc4_step x

def f406desc5 : Matrix (Fin 27) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-9/10), (9/10), (9/10);
    (-3/2), (1/2), (1/6);
    (-5/2), (-1/2), (-13/6);
    (-2), 1, (-8/3);
    (4/5), (21/5), (-4/5);
    0, 1, (4/3);
    3, (-5), (-11/3);
    (-4), (-8), (-20/3);
    2, 0, 4;
    (36/5), (14/5), (92/15);
    (-3), (-4), (-1/3);
    (-26), 4, (46/3);
    0, 8, (62/3);
    (-6), 8, (14/3);
    15, 5, (-25/3);
    6, (-1), (-2/3);
    24, (-4), (-16/3);
    4, (-4), (-4/3);
    18, (-22), (-10/3);
    (-9), 24, 11;
    (-48), 16, (-8/3);
    15, (-35), (-95/3);
    30, (-40), (-190/3);
    (-27), 28, 17;
    (-15), 20, (95/3);
    20, 0, 20]

theorem f406desc5_step : f410raise*f406desc4=f406desc5 := by
  refine natFourSparseRowProduct_matrix_check f410raise f406desc4 f406desc5
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 0) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 1) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 2) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 3) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 4) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 5) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 6) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 7) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 8) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 9) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 10) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 11) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 12) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 13) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 14) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 15) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 16) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 17) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 18) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 19) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 20) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 21) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 22) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 23) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 24) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 25) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f410raiseSparseRows 26) f406desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc5 26 b)
      (by decide +kernel) 0 b

theorem f406desc5_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f406desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f410basis f411basis f406desc4 f406desc5 f410raise
    f406desc4_actual f410_actual_raise_block f406desc5_step x

#print axioms f406desc2_step
#print axioms f406desc2_actual
#print axioms f406desc3_step
#print axioms f406desc3_actual
#print axioms f406desc4_step
#print axioms f406desc4_actual
#print axioms f406desc5_step
#print axioms f406desc5_actual
end TorusLean.BosonFiniteCertificate
