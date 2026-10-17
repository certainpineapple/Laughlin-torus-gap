import torus.shared.BosonFiniteCertificateNatFourRaiseSparse404
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse405
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise404
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
import torus.shared.BosonFiniteCertificate404

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

def f404desc0 : Matrix (Fin 5) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (-4/3), (4/3);
    1, 0;
    0, (-2);
    0, 1]

theorem f404desc0_root : f404desc0=b404relative := by
  decide +kernel

theorem f404desc0_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f404basis (complexify f404desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f404desc0_root]

def f404desc1 : Matrix (Fin 6) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (-1/3), (1/3);
    (2/3), (4/3);
    (-8/3), (2/3);
    2, (-4);
    0, 2]

theorem f404desc1_step : f404raise*f404desc0=f404desc1 := by
  refine natFourSparseRowProduct_matrix_check f404raise f404desc0 f404desc1
    f404raiseSparseRows f404_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f404raiseSparseRows 0) f404desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f404raiseSparseRows 1) f404desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f404raiseSparseRows 2) f404desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f404raiseSparseRows 3) f404desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f404raiseSparseRows 4) f404desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f404raiseSparseRows 5) f404desc0 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc1 5 b)
      (by decide +kernel) 0 b

theorem f404desc1_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f405basis (complexify f404desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f404basis f405basis f404desc0 f404desc1 f404raise
    f404desc0_actual f404_actual_raise_block f404desc1_step x

def f404desc2 : Matrix (Fin 9) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (2/3), (-2/3);
    (1/3), (5/3);
    (2/3), (4/3);
    (-10/3), (4/3);
    0, (-4);
    2, (-4);
    (-8/3), (8/3);
    2, 2]

theorem f404desc2_step : f405raise*f404desc1=f404desc2 := by
  refine natFourSparseRowProduct_matrix_check f405raise f404desc1 f404desc2
    f405raiseSparseRows f405_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 0) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 1) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 2) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 3) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 4) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 5) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 6) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 7) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f405raiseSparseRows 8) f404desc1 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc2 8 b)
      (by decide +kernel) 0 b

theorem f404desc2_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f406basis (complexify f404desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f405basis f406basis f404desc1 f404desc2 f405raise
    f404desc1_actual f405_actual_raise_block f404desc2_step x

def f404desc3 : Matrix (Fin 11) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (5/3), (-5/3);
    1, 1;
    (5/3), (13/3);
    (-2), 0;
    (-6), 2;
    (4/3), (-4/3);
    6, (-16);
    (-6), 4;
    (-4), 8;
    6, 0]

theorem f404desc3_step : f406raise*f404desc2=f404desc3 := by
  refine natFourSparseRowProduct_matrix_check f406raise f404desc2 f404desc3
    f406raiseSparseRows f406_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 0) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 1) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 2) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 3) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 4) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 5) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 6) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 7) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 8) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 9) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f406raiseSparseRows 10) f404desc2 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc3 10 b)
      (by decide +kernel) 0 b

theorem f404desc3_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f404desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f406basis f407basis f404desc2 f404desc3 f406raise
    f404desc2_actual f406_actual_raise_block f404desc3_step x

#print axioms f404desc0_root
#print axioms f404desc0_actual
#print axioms f404desc1_step
#print axioms f404desc1_actual
#print axioms f404desc2_step
#print axioms f404desc2_actual
#print axioms f404desc3_step
#print axioms f404desc3_actual
end TorusLean.BosonFiniteCertificate
