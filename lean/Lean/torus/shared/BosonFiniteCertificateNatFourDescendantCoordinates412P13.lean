import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate412

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

def f412desc0 : Matrix (Fin 34) (Fin 7) ℚ :=
  !![(1/462), (-1/462), (1/330), (-1/462), (1/330), (1/330), (-1/165);
    (-2/77), (2/77), (-2/55), (2/77), (-2/55), (-2/55), (4/55);
    (1/7), (-1/14), (3/35), (-4/63), (13/210), (17/315), (-1/10);
    (-10/21), (5/42), (-2/21), (5/42), (-11/210), (-4/105), (1/21);
    (15/14), (-5/42), (3/70), (-5/42), (1/70), (1/70), 0;
    (-12/7), (1/21), 0, (1/21), 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, (-1/14), (4/35), (-5/63), (29/210), (46/315), (-3/10);
    0, (5/14), (-4/7), (5/18), (-97/210), (-134/315), (6/7);
    0, (-25/42), (24/35), (-25/42), (29/70), (2/7), (-3/7);
    0, (5/7), (-12/35), (5/7), (-4/35), (-4/35), 0;
    0, (-1/3), 0, (-1/3), 0, 0, 0;
    0, (-5/14), (27/35), 0, (27/70), (2/7), (-9/14);
    0, (20/21), (-72/35), 0, (-26/35), (-32/105), (24/35);
    0, (-5/3), (6/5), 0, (1/5), (2/15), 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, (8/5), 0, (2/5), 0, (-1/5);
    0, 0, (-12/5), 0, (-1/5), 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, (5/63), (-16/105), (-64/315), (3/7);
    0, 0, 0, (-5/14), (24/35), (32/35), (-27/14);
    0, 0, 0, (20/21), (-24/35), (-64/105), (36/35);
    0, 0, 0, (-5/3), (1/5), (4/15), 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, (-6/7), (-48/35), (108/35);
    0, 0, 0, 0, 2, (8/5), (-18/5);
    0, 0, 0, 0, (-3/5), (-4/5), 0;
    0, 0, 0, 0, (-8/5), 0, (6/5);
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, (4/5), (-9/5);
    0, 0, 0, 0, 0, (-8/5), (18/5);
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, (-3);
    0, 0, 0, 0, 0, 0, 1]

theorem f412desc0_root : f412desc0=b412relative := by
  decide +kernel

theorem f412desc0_actual (x : Fin 7 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f412basis (complexify b412relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f412desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f412desc0_root]

def f412desc1 : Matrix (Fin 39) (Fin 7) ℚ :=
  !![(1/462), (-1/462), (1/330), (-1/462), (1/330), (1/330), (-1/165);
    (-3/154), (3/154), (-3/110), (3/154), (-3/110), (-3/110), (3/55);
    (9/77), (-1/22), (19/385), (-26/693), (59/2310), (61/3465), (-3/110);
    (-1/3), (1/21), (-1/105), (1/18), (1/105), (1/63), (-11/210);
    (25/42), 0, (-11/210), 0, (-4/105), (-1/42), (1/21);
    (-9/14), (-1/14), (3/70), (-1/14), (1/70), (1/70), 0;
    (2/7), (1/21), 0, (1/21), 0, 0, 0;
    (-4/77), (-3/154), (16/385), (-19/693), (151/2310), (254/3465), (-17/110);
    (2/7), (1/14), (-6/35), (-1/126), (-13/210), (-8/315), (2/35);
    (-20/21), 0, (-8/105), (-5/63), (-16/105), (-68/315), (11/21);
    (15/7), (-5/42), (3/7), (-5/42), (23/70), (1/5), (-3/7);
    (-24/7), (10/21), (-12/35), (10/21), (-4/35), (-4/35), 0;
    2, (-1/3), 0, (-1/3), 0, 0, 0;
    0, 0, (1/5), (5/18), (-8/105), (-44/315), (3/14);
    0, (-5/14), (6/35), (-25/42), (31/70), (58/105), (-36/35);
    0, 0, (-6/5), (5/7), (-23/35), (-2/7), (24/35);
    0, 0, (6/5), (-1/3), (1/5), (2/15), 0;
    0, (20/21), (-16/35), 0, (-12/35), (-32/105), (17/35);
    0, (-5/3), 2, 0, (4/5), (2/15), (-2/5);
    0, 1, (-12/5), 0, (-1/5), 0, 0;
    0, 0, (3/5), 0, (-1/5), 0, 0;
    0, (-1/14), (4/35), 0, (-1/70), (-2/35), (9/70);
    0, (5/14), (-4/7), (10/63), (-7/30), (-38/315), (3/14);
    0, (-25/42), (24/35), 0, (29/70), (62/105), (-93/70);
    0, (5/7), (-12/35), 0, (-3/5), (-16/35), (36/35);
    0, (-1/3), 0, 0, (1/5), (4/15), 0;
    0, (-5/14), (27/35), (-5/7), (9/10), (26/35), (-99/70);
    0, (20/21), (-72/35), (40/21), (-64/35), (-8/3), (186/35);
    0, (-5/3), (6/5), (-10/3), 2, (22/15), (-18/5);
    0, 1, 0, 2, (-3/5), (-4/5), 0;
    0, 0, (8/5), 0, (4/5), (8/5), (-13/5);
    0, 0, (-12/5), 0, (-2), (-4/5), (12/5);
    0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, (-6/7), (-4/7), (9/7);
    0, 0, 0, 0, 2, (12/5), (-27/5);
    0, 0, 0, 0, (-3/5), (-2/5), (18/5);
    0, 0, 0, 0, (-8/5), (-16/5), (27/5);
    0, 0, 0, 0, 1, 2, (-6);
    0, 0, 0, 0, 0, 0, 1]

theorem f412desc1_step : f412raise*f412desc0=f412desc1 := by
  refine natFourSparseRowProduct_matrix_check f412raise f412desc0 f412desc1
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 0) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 1) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 2) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 3) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 4) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 5) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 6) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 7) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 8) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 9) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 10) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 11) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 12) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 13) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 14) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 15) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 16) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 17) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 18) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 19) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 20) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 21) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 22) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 23) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 24) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 25) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 26) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 27) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 28) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 29) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 30) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 31) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 32) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 33) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 34) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 35) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 36) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 37) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f412raiseSparseRows 38) f412desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc1 38 b)
      (by decide +kernel) 0 b

theorem f412desc1_actual (x : Fin 7 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f412basis (complexify b412relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f412desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f412basis (complexify b412relative *ᵥ x))
    f412basis f413basis f412desc0 f412desc1 f412raise
    f412desc0_actual f412_actual_raise_block f412desc1_step x

#print axioms f412desc0_root
#print axioms f412desc0_actual
#print axioms f412desc1_step
#print axioms f412desc1_actual
end TorusLean.BosonFiniteCertificate
