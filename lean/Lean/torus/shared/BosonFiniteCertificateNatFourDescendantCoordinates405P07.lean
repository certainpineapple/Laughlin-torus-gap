import torus.shared.BosonFiniteCertificateNatFourRaiseSparse405
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise405
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
import torus.shared.BosonFiniteCertificate405

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

def f405desc0 : Matrix (Fin 6) (Fin 1) ℚ :=
  !![(-1/6);
    (5/6);
    (-1/3);
    (-4/3);
    1;
    0]

theorem f405desc0_root : f405desc0=b405relative := by
  decide +kernel

theorem f405desc0_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f405basis (complexify f405desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f405desc0_root]

def f405desc1 : Matrix (Fin 9) (Fin 1) ℚ :=
  !![(-1/6);
    (1/3);
    (1/2);
    (-1/3);
    (1/3);
    (-4/3);
    1;
    (-4/3);
    1]

theorem f405desc1_step : f405raise*f405desc0=f405desc1 := by
  refine natFourSparseRowProduct_matrix_check f405raise f405desc0 f405desc1
    f405raiseSparseRows f405_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 0) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 1) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 2) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 3) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 4) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 5) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 6) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 7) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 8) f405desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc1 8 b)
      (by decide +kernel) 0 b

theorem f405desc1_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f406basis (complexify f405desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f405basis f406basis f405desc0 f405desc1 f405raise
    f405desc0_actual f405_actual_raise_block f405desc1_step x

def f405desc2 : Matrix (Fin 11) (Fin 1) ℚ :=
  !![(-1/6);
    (-1/6);
    (5/6);
    (-1/6);
    1;
    (1/3);
    (-2);
    (5/3);
    (-1);
    (-10/3);
    3]

theorem f405desc2_step : f406raise*f405desc1=f405desc2 := by
  refine natFourSparseRowProduct_matrix_check f406raise f405desc1 f405desc2
    f406raiseSparseRows f406_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 0) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 1) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 2) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 3) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 4) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 5) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 6) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 7) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 8) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 9) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 10) f405desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc2 10 b)
      (by decide +kernel) 0 b

theorem f405desc2_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f405desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f406basis f407basis f405desc1 f405desc2 f406raise
    f405desc1_actual f406_actual_raise_block f405desc2_step x

#print axioms f405desc0_root
#print axioms f405desc0_actual
#print axioms f405desc1_step
#print axioms f405desc1_actual
#print axioms f405desc2_step
#print axioms f405desc2_actual
end TorusLean.BosonFiniteCertificate
