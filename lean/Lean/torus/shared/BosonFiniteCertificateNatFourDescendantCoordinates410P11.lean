import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate410

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

def f410desc0 : Matrix (Fin 23) (Fin 5) ℚ :=
  !![(-1/126), (1/126), (1/126), (-1/84), (-1/84);
    (5/63), (-5/63), (-5/63), (5/42), (5/42);
    (-5/14), (11/70), (9/70), (-3/20), (-17/140);
    (20/21), (-16/105), (-16/105), (11/140), (1/35);
    (-5/3), (1/15), (1/15), 0, 0;
    1, 0, 0, 0, 0;
    0, (1/5), (8/35), (-27/70), (-29/70);
    0, (-4/5), (-4/7), (27/28), (31/35);
    0, (4/5), (4/5), (-11/20), (-1/5);
    0, (-2/5), (-2/5), 0, 0;
    0, (4/5), 0, (-3/5), (-1/2);
    0, (-8/5), 0, (3/4), (1/5);
    0, 1, 0, 0, 0;
    0, 0, 0, (-1/4), 0;
    0, 0, (-8/35), (27/70), (18/35);
    0, 0, (4/5), (-27/20), (-9/5);
    0, 0, (-8/5), (9/10), (2/5);
    0, 0, 1, 0, 0;
    0, 0, 0, (27/20), (12/5);
    0, 0, 0, (-9/4), (-1);
    0, 0, 0, 1, 0;
    0, 0, 0, 0, (-3/2);
    0, 0, 0, 0, 1]

theorem f410desc0_root : f410desc0=b410relative := by
  decide +kernel

theorem f410desc0_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f410desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f410desc0_root]

def f410desc1 : Matrix (Fin 27) (Fin 5) ℚ :=
  !![(-1/126), (1/126), (1/126), (-1/84), (-1/84);
    (1/18), (-1/18), (-1/18), (1/12), (1/12);
    (-5/18), (7/90), (31/630), (-13/420), (-1/420);
    (25/42), (1/210), (-1/42), (-1/14), (-13/140);
    (-5/7), (-3/35), (-3/35), (11/140), (1/35);
    (1/3), (1/15), (1/15), 0, 0;
    (10/63), (13/315), (22/315), (-31/210), (-37/210);
    (-5/7), (-3/35), (1/7), (-3/28), (-13/70);
    (40/21), (-32/105), (-8/105), (4/7), (26/35);
    (-10/3), (8/15), (8/15), (-11/20), (-1/5);
    2, (-2/5), (-2/5), 0, 0;
    0, 0, (-4/7), (51/140), (27/70);
    0, (4/5), (4/5), (-1), (-1);
    0, 0, (-2/5), (3/4), (1/5);
    0, (-8/5), 0, (1/2), (1/5);
    0, 1, 0, (-1/2), 0;
    0, (1/5), 0, 0, (1/10);
    0, (-4/5), (-16/35), (27/35), (22/35);
    0, (4/5), 0, (-1), (-8/5);
    0, (-2/5), 0, (9/10), (2/5);
    0, (4/5), (8/5), (-39/20), (-17/10);
    0, (-8/5), (-16/5), 3, (24/5);
    0, 1, 2, (-9/4), (-1);
    0, 0, 0, (1/2), (-1);
    0, 0, 0, (27/20), (9/10);
    0, 0, 0, (-9/4), (-7/2);
    0, 0, 0, 1, 2]

theorem f410desc1_step : f410raise*f410desc0=f410desc1 := by
  refine natFourSparseRowProduct_matrix_check f410raise f410desc0 f410desc1
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 0) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 1) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 2) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 3) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 4) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 5) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 6) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 7) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 8) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 9) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 10) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 11) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 12) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 13) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 14) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 15) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 16) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 17) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 18) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 19) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 20) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 21) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 22) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 23) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 24) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 25) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f410raiseSparseRows 26) f410desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc1 26 b)
      (by decide +kernel) 0 b

theorem f410desc1_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f410desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f410basis (complexify b410relative *ᵥ x))
    f410basis f411basis f410desc0 f410desc1 f410raise
    f410desc0_actual f410_actual_raise_block f410desc1_step x

#print axioms f410desc0_root
#print axioms f410desc0_actual
#print axioms f410desc1_step
#print axioms f410desc1_actual
end TorusLean.BosonFiniteCertificate
