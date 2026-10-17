import torus.shared.BosonFiniteCertificateNatFourRaiseSparse403
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse404
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse405
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise403
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
import torus.shared.BosonFiniteCertificate403

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

def f403desc0 : Matrix (Fin 3) (Fin 1) ℚ :=
  !![(1/2);
    (-3/2);
    1]

theorem f403desc0_root : f403desc0=b403relative := by
  decide +kernel

theorem f403desc0_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f403basis (complexify f403desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f403desc0_root]

def f403desc1 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![(1/2);
    0;
    (-3/2);
    0;
    1]

theorem f403desc1_step : f403raise*f403desc0=f403desc1 := by
  refine natFourSparseRowProduct_matrix_check f403raise f403desc0 f403desc1
    f403raiseSparseRows f403_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f403raiseSparseRows 0) f403desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f403raiseSparseRows 1) f403desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f403raiseSparseRows 2) f403desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f403raiseSparseRows 3) f403desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f403raiseSparseRows 4) f403desc0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc1 4 b)
      (by decide +kernel) 0 b

theorem f403desc1_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f404basis (complexify f403desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f403basis f404basis f403desc0 f403desc1 f403raise
    f403desc0_actual f403_actual_raise_block f403desc1_step x

def f403desc2 : Matrix (Fin 6) (Fin 1) ℚ :=
  !![(1/2);
    (3/2);
    (-3);
    0;
    (-3);
    4]

theorem f403desc2_step : f404raise*f403desc1=f403desc2 := by
  refine natFourSparseRowProduct_matrix_check f404raise f403desc1 f403desc2
    f404raiseSparseRows f404_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f404raiseSparseRows 0) f403desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f404raiseSparseRows 1) f403desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f404raiseSparseRows 2) f403desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f404raiseSparseRows 3) f403desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f404raiseSparseRows 4) f403desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f404raiseSparseRows 5) f403desc1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc2 5 b)
      (by decide +kernel) 0 b

theorem f403desc2_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f405basis (complexify f403desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f404basis f405basis f403desc1 f403desc2 f404raise
    f403desc1_actual f404_actual_raise_block f403desc2_step x

def f403desc3 : Matrix (Fin 9) (Fin 1) ℚ :=
  !![(1/2);
    3;
    (-3/2);
    (-3);
    3;
    (-12);
    (-3);
    4;
    9]

theorem f403desc3_step : f405raise*f403desc2=f403desc3 := by
  refine natFourSparseRowProduct_matrix_check f405raise f403desc2 f403desc3
    f405raiseSparseRows f405_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 0) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 1) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 2) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 3) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 4) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 5) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 6) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 7) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f405raiseSparseRows 8) f403desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc3 8 b)
      (by decide +kernel) 0 b

theorem f403desc3_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f406basis (complexify f403desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f405basis f406basis f403desc2 f403desc3 f405raise
    f403desc2_actual f405_actual_raise_block f403desc3_step x

def f403desc4 : Matrix (Fin 11) (Fin 1) ℚ :=
  !![(1/2);
    (9/2);
    (3/2);
    (-15/2);
    9;
    (-9);
    (-18);
    (-21);
    7;
    18;
    15]

theorem f403desc4_step : f406raise*f403desc3=f403desc4 := by
  refine natFourSparseRowProduct_matrix_check f406raise f403desc3 f403desc4
    f406raiseSparseRows f406_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 0) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 1) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 2) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 3) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 4) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 5) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 6) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 7) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 8) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 9) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f406raiseSparseRows 10) f403desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc4 10 b)
      (by decide +kernel) 0 b

theorem f403desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f403desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f406basis f407basis f403desc3 f403desc4 f406raise
    f403desc3_actual f406_actual_raise_block f403desc4_step x

#print axioms f403desc0_root
#print axioms f403desc0_actual
#print axioms f403desc1_step
#print axioms f403desc1_actual
#print axioms f403desc2_step
#print axioms f403desc2_actual
#print axioms f403desc3_step
#print axioms f403desc3_actual
#print axioms f403desc4_step
#print axioms f403desc4_actual
end TorusLean.BosonFiniteCertificate
