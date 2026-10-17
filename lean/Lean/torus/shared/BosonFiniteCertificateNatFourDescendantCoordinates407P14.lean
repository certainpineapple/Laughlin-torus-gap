import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407P13

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

def f407desc7 : Matrix (Fin 47) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (7/10), (-14/15);
    (23/20), (-6/5);
    (4/5), (14/15);
    (9/20), (56/15);
    (1/10), (38/15);
    (-7/4), (-7/3);
    (-8/5), (-38/15);
    2, (-3);
    (3/5), (-22/15);
    (-5), 14;
    2, (46/3);
    (27/5), (-16/5);
    (-42/5), (-84/5);
    (-42/5), (31/5);
    (-21), (26/3);
    (-3/2), (-52/3);
    (-18), (4/3);
    (-112/5), (238/15);
    (-6), (-70/3);
    (-4), (-112/3);
    (-182/5), (1148/15);
    (7/2), (98/3);
    (42/5), (1162/15);
    0, (-4/3);
    (-63/5), (152/15);
    0, 12;
    42, (-47/3);
    (192/5), (-248/15);
    7, 0;
    (-21), (44/3);
    63, (-74);
    114, (-92);
    (-168/5), (504/5);
    64, (-112);
    70, (-196);
    0, (-56);
    105, (-728/3);
    0, 1;
    0, (104/3);
    (-126), (574/3);
    (-567/5), (756/5);
    (-140), (560/3);
    (-210), (532/3);
    (105/2), (-280/3);
    0, (112/3);
    210, (-490/3)]

theorem f407desc7_step : f413raise*f407desc6=f407desc7 := by
  refine natFourSparseRowProduct_matrix_check f413raise f407desc6 f407desc7
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 0) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 1) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 2) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 3) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 4) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 5) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 6) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 7) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 8) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 9) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 10) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 11) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 12) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 13) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 14) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 15) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 16) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 17) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 18) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 19) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 20) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 21) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 22) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 23) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 24) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 25) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 26) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 27) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 28) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 29) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 30) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 31) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 32) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 33) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 34) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 35) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 36) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 37) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 38) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 39) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 40) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 41) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 42) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 43) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 44) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 45) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 46) f407desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc7 46 b)
      (by decide +kernel) 0 b

theorem f407desc7_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f407desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f413basis f414basis f407desc6 f407desc7 f413raise
    f407desc6_actual f413_actual_raise_block f407desc7_step x

#print axioms f407desc7_step
#print axioms f407desc7_actual
end TorusLean.BosonFiniteCertificate
