import torus.shared.BosonFiniteCertificateNatFourRaiseSparse408
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse409
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate408

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

def f408desc0 : Matrix (Fin 15) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (-8/35), (8/35), (8/35), (-8/21);
    (4/5), (-3/10), (-1/5), (4/15);
    (-8/5), (1/10), (1/10), 0;
    1, 0, 0, 0;
    0, (-1/2), (-3/5), (16/15);
    0, (3/2), (9/10), (-8/5);
    0, (-1/2), (-1/2), 0;
    0, (-3/2), 0, (2/3);
    0, 1, 0, 0;
    0, 0, (3/5), (-16/15);
    0, 0, (-3/2), (8/3);
    0, 0, 1, 0;
    0, 0, 0, (-8/3);
    0, 0, 0, 1]

theorem f408desc0_root : f408desc0=b408relative := by
  decide +kernel

theorem f408desc0_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f408desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f408desc0_root]

def f408desc1 : Matrix (Fin 18) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (-1/7), (1/7), (1/7), (-5/21);
    (4/7), (-1/14), (1/35), (-4/35);
    (-4/5), (-1/5), (-1/10), (4/15);
    (2/5), (1/10), (1/10), 0;
    (-16/35), (-3/70), (-1/7), (32/105);
    (8/5), (-1/10), (-7/10), (16/15);
    (-16/5), (6/5), (3/5), (-8/5);
    2, (-1/2), (-1/2), 0;
    0, 0, (9/10), (-14/15);
    0, (-3/2), (-1/2), (4/3);
    0, 1, 0, 0;
    0, (-1/2), 0, 0;
    0, (3/2), (6/5), (-32/15);
    0, (-1/2), 0, (8/3);
    0, (-3/2), (-3), (10/3);
    0, 1, 2, (-16/3);
    0, 0, 0, (4/3)]

theorem f408desc1_step : f408raise*f408desc0=f408desc1 := by
  refine natFourSparseRowProduct_matrix_check f408raise f408desc0 f408desc1
    f408raiseSparseRows f408_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 0) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 1) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 2) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 3) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 4) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 5) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 6) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 7) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 8) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 9) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 10) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 11) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 12) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 13) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 14) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 15) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 16) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f408raiseSparseRows 17) f408desc0 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc1 17 b)
      (by decide +kernel) 0 b

theorem f408desc1_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f408desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f408basis (complexify b408relative *ᵥ x))
    f408basis f409basis f408desc0 f408desc1 f408raise
    f408desc0_actual f408_actual_raise_block f408desc1_step x

def f408desc2 : Matrix (Fin 23) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (-2/35), (2/35), (2/35), (-2/21);
    (3/7), (1/14), (6/35), (-37/105);
    (-8/35), (-19/70), (-1/14), (16/105);
    (-2/5), (-1/10), 0, (4/15);
    (2/5), (1/10), (1/10), 0;
    (-26/35), (17/70), (1/7), (-6/35);
    (64/35), (-23/70), (-13/14), (152/105);
    (-16/5), (7/10), (-3/10), 0;
    (8/5), (2/5), (-1/5), (-8/5);
    (8/5), (-1/10), (1/5), (2/15);
    (-16/5), (-3/10), (19/10), (-32/15);
    2, (-2), (-1), (4/3);
    0, (3/2), (-1/2), (4/3);
    (-16/35), (-19/35), (-1/7), (32/105);
    (8/5), (-1/10), (1/2), (-16/15);
    (-16/5), (11/5), (9/5), (-16/15);
    2, (-1), (-1/2), (8/3);
    0, (3/2), (3/10), (-28/15);
    0, (-7/2), (-5/2), (8/3);
    0, 2, 2, (-16/3);
    0, (-3/2), (-3), (14/3);
    0, 1, 2, (-4/3)]

theorem f408desc2_step : f409raise*f408desc1=f408desc2 := by
  refine natFourSparseRowProduct_matrix_check f409raise f408desc1 f408desc2
    f409raiseSparseRows f409_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 0) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 1) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 2) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 3) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 4) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 5) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 6) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 7) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 8) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 9) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 10) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 11) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 12) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 13) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 14) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 15) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 16) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 17) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 18) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 19) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 20) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 21) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f409raiseSparseRows 22) f408desc1 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc2 22 b)
      (by decide +kernel) 0 b

theorem f408desc2_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f408desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f408basis (complexify b408relative *ᵥ x))
    f409basis f410basis f408desc1 f408desc2 f409raise
    f408desc1_actual f409_actual_raise_block f408desc2_step x

def f408desc3 : Matrix (Fin 27) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (1/35), (-1/35), (-1/35), (1/21);
    (13/35), (9/70), (8/35), (-47/105);
    (1/5), (-1/5), (1/10), (-1/5);
    (-22/35), (-13/35), (-1/14), (44/105);
    (2/5), (1/10), (1/5), (4/15);
    (-6/7), (5/14), (9/35), (-38/105);
    (6/5), (3/10), (-3/10), (2/5);
    (-64/35), (-6/35), (-48/35), (184/105);
    (-12/5), (9/10), (-1/2), (-16/15);
    (12/5), (3/5), 0, (-8/5);
    (24/7), (-3/7), (-51/70), (166/105);
    (-16/5), (1/5), 2, (-28/15);
    (12/5), (-39/10), (-3/10), (-16/15);
    (-16/5), (6/5), (7/5), (-4/5);
    2, 1, (-2), 4;
    (-6/5), (-3/10), 0, (2/15);
    (72/35), (-72/35), (-6/7), (136/105);
    (-24/5), (14/5), 2, (-32/15);
    (12/5), (3/5), (3/5), (8/3);
    (24/5), (6/5), (3/2), (-58/15);
    (-48/5), (18/5), (18/5), (-16/3);
    6, (-15/2), (-9/2), (28/3);
    0, 4, 3, (-12);
    0, 0, (-27/10), (14/5);
    0, (-6), (-15/2), 14;
    0, 4, 6, (-8)]

theorem f408desc3_step : f410raise*f408desc2=f408desc3 := by
  refine natFourSparseRowProduct_matrix_check f410raise f408desc2 f408desc3
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 0) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 1) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 2) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 3) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 4) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 5) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 6) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 7) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 8) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 9) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 10) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 11) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 12) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 13) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 14) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 15) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 16) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 17) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 18) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 19) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 20) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 21) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 22) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 23) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 24) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 25) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f410raiseSparseRows 26) f408desc2 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc3 26 b)
      (by decide +kernel) 0 b

theorem f408desc3_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f408desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f408basis (complexify b408relative *ᵥ x))
    f410basis f411basis f408desc2 f408desc3 f410raise
    f408desc2_actual f410_actual_raise_block f408desc3_step x

#print axioms f408desc0_root
#print axioms f408desc0_actual
#print axioms f408desc1_step
#print axioms f408desc1_actual
#print axioms f408desc2_step
#print axioms f408desc2_actual
#print axioms f408desc3_step
#print axioms f408desc3_actual
end TorusLean.BosonFiniteCertificate
