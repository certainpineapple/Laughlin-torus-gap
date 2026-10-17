import torus.shared.BosonFiniteCertificateNatFourRaiseSparse406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise406
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate406

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

def f406desc0 : Matrix (Fin 9) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (3/5), (-3/5), (-3/5);
    (-3/2), (1/2), (1/6);
    1, 0, 0;
    0, 1, (4/3);
    0, (-2), (-2/3);
    0, 1, 0;
    0, 0, (-4/3);
    0, 0, 1]

theorem f406desc0_root : f406desc0=b406relative := by
  decide +kernel

theorem f406desc0_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f406basis (complexify f406desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f406desc0_root]

def f406desc1 : Matrix (Fin 11) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (3/10), (-3/10), (-3/10);
    (-9/10), (-1/10), (-13/30);
    (1/2), (1/2), (1/6);
    (6/5), (-1/5), (2/15);
    (-3), 1, (7/3);
    2, (-2), (-2/3);
    0, 1, (-2/3);
    0, 1, 0;
    0, (-2), (-8/3);
    0, 1, 2]

theorem f406desc1_step : f406raise*f406desc0=f406desc1 := by
  refine natFourSparseRowProduct_matrix_check f406raise f406desc0 f406desc1
    f406raiseSparseRows f406_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 0) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 1) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 2) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 3) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 4) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 5) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 6) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 7) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 8) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 9) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f406raiseSparseRows 10) f406desc0 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc1 10 b)
      (by decide +kernel) 0 b

theorem f406desc1_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f406desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f406basis f407basis f406desc0 f406desc1 f406raise
    f406desc0_actual f406_actual_raise_block f406desc1_step x

#print axioms f406desc0_root
#print axioms f406desc0_actual
#print axioms f406desc1_step
#print axioms f406desc1_actual
end TorusLean.BosonFiniteCertificate
