import torus.shared.BosonFiniteCertificateNatFourRaiseSparse407
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse408
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse409
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407P07

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

def f407desc1 : Matrix (Fin 15) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (-1/5), (4/15);
    (1/10), (1/5);
    (1/5), (-4/15);
    (-1/4), 0;
    (-1/10), (-1/5);
    (3/5), (-22/15);
    0, (4/3);
    (-3/2), 1;
    1, (-2/3);
    (3/5), (-2/15);
    (-3/2), (7/3);
    1, (-2);
    0, (-4/3);
    0, 1]

theorem f407desc1_step : f407raise*f407desc0=f407desc1 := by
  refine natFourSparseRowProduct_matrix_check f407raise f407desc0 f407desc1
    f407raiseSparseRows f407_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 0) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 1) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 2) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 3) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 4) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 5) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 6) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 7) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 8) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 9) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 10) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 11) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 12) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 13) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 14) f407desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc1 14 b)
      (by decide +kernel) 0 b

theorem f407desc1_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f407desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f407basis f408basis f407desc0 f407desc1 f407raise
    f407desc0_actual f407_actual_raise_block f407desc1_step x

def f407desc2 : Matrix (Fin 18) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (-1/20), (1/15);
    (-1/10), (7/15);
    (3/10), (-1/15);
    (-3/10), (-4/15);
    (-1/2), (1/3);
    (3/5), (-22/15);
    1, (-2/3);
    (-1/2), (4/3);
    (-9/10), (-7/15);
    (-1), 2;
    1, (-2/3);
    (1/2), (-1/3);
    (9/10), (7/15);
    (1/2), (-1/3);
    (-9/2), (13/3);
    3, (-22/3);
    0, (8/3)]

theorem f407desc2_step : f408raise*f407desc1=f407desc2 := by
  refine natFourSparseRowProduct_matrix_check f408raise f407desc1 f407desc2
    f408raiseSparseRows f408_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 0) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 1) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 2) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 3) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 4) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 5) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 6) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 7) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 8) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 9) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 10) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 11) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 12) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 13) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 14) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 15) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 16) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 17) f407desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc2 17 b)
      (by decide +kernel) 0 b

theorem f407desc2_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f407desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f408basis f409basis f407desc1 f407desc2 f408raise
    f407desc1_actual f408_actual_raise_block f407desc2_step x

def f407desc3 : Matrix (Fin 23) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (1/10), (-2/15);
    (-3/20), (8/15);
    (1/5), (2/5);
    0, (-1/3);
    (-3/10), (-4/15);
    (-3/5), (7/15);
    (-3/5), (2/15);
    (11/5), (-34/15);
    (-3/5), (22/15);
    (-3/10), (-29/15);
    (-9/5), (2/5);
    (-3/2), (10/3);
    2, 0;
    0, 0;
    3, (-2);
    (12/5), (-8/15);
    0, 1;
    (-18/5), (24/5);
    (-3), (-14/3);
    4, (-8);
    (-9/2), 7;
    3, (2/3)]

theorem f407desc3_step : f409raise*f407desc2=f407desc3 := by
  refine natFourSparseRowProduct_matrix_check f409raise f407desc2 f407desc3
    f409raiseSparseRows f409_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 0) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 1) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 2) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 3) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 4) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 5) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 6) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 7) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 8) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 9) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 10) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 11) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 12) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 13) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 14) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 15) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 16) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 17) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 18) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 19) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 20) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 21) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 22) f407desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc3 22 b)
      (by decide +kernel) 0 b

theorem f407desc3_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f407desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f409basis f410basis f407desc2 f407desc3 f409raise
    f407desc2_actual f409_actual_raise_block f407desc3_step x

def f407desc4 : Matrix (Fin 27) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (1/4), (-1/3);
    (-1/20), (2/5);
    (1/20), (14/15);
    (1/5), (1/15);
    (-3/5), (-13/15);
    (-2/5), (1/5);
    (-21/10), (32/15);
    2, (-4/3);
    (8/5), (-22/15);
    (-6/5), (14/15);
    (-9/10), (-9/5);
    (-1/5), (-86/15);
    (-27/5), (128/15);
    (1/5), (2/5);
    (5/2), (10/3);
    (-3/5), (7/15);
    (12/5), (-28/15);
    (38/5), (-24/5);
    (9/5), (44/15);
    (21/10), (-17/15);
    (-36/5), (64/15);
    (-9/2), (2/3);
    11, (-86/3);
    (-81/10), (59/5);
    (-21/2), (53/3);
    10, (-20/3)]

theorem f407desc4_step : f410raise*f407desc3=f407desc4 := by
  refine natFourSparseRowProduct_matrix_check f410raise f407desc3 f407desc4
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 0) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 1) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 2) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 3) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 4) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 5) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 6) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 7) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 8) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 9) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 10) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 11) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 12) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 13) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 14) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 15) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 16) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 17) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 18) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 19) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 20) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 21) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 22) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 23) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 24) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 25) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 26) f407desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc4 26 b)
      (by decide +kernel) 0 b

theorem f407desc4_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f407desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f410basis f411basis f407desc3 f407desc4 f410raise
    f407desc3_actual f410_actual_raise_block f407desc4_step x

#print axioms f407desc1_step
#print axioms f407desc1_actual
#print axioms f407desc2_step
#print axioms f407desc2_actual
#print axioms f407desc3_step
#print axioms f407desc3_actual
#print axioms f407desc4_step
#print axioms f407desc4_actual
end TorusLean.BosonFiniteCertificate
