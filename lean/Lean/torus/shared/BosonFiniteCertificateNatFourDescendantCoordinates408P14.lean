import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408P13

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

def f408desc6 : Matrix (Fin 47) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (2/7), (-2/7), (-2/7), (10/21);
    (5/7), (-3/14), (-4/35), (13/105);
    (52/35), (1/70), (43/70), (-44/35);
    (39/35), (-43/70), (31/35), (-31/21);
    (-18/35), (-52/35), (18/35), (10/21);
    (-3/35), (-32/35), (24/35), (223/105);
    (4/7), (-1/14), (37/70), (128/105);
    (-6/35), (-23/70), (-3/7), (82/105);
    (-24/35), (153/70), (111/70), (-96/35);
    (88/35), (209/70), (167/70), (-568/105);
    (-36/7), (-13/7), (-20/7), (44/21);
    (-372/35), (-48/35), (-174/35), (164/35);
    (32/5), (33/5), (-1/5), (-24/5);
    (30/7), (45/14), (39/35), (-188/105);
    (152/7), (25/14), (-73/14), (200/21);
    (-18/7), (-45/7), (-66/7), (274/21);
    0, (-9), (-3), (-40/3);
    (68/5), (-23/5), (4/5), (-244/15);
    (44/7), (-11/14), (-25/14), (64/7);
    (-32), (-2), 10, (-8/3);
    (16/5), (-61/5), (17/5), (-176/15);
    (-10), 4, (-1), (40/3);
    (84/5), (21/5), (-84/5), (112/3);
    (-24/7), (3/7), (3/7), (-8/21);
    (-108/7), (27/14), (219/70), (-404/105);
    (-72/7), (-19/7), (-19/7), (88/21);
    (-186/7), (15/14), (-45/7), (218/21);
    (-48/5), (78/5), (6/5), (-16/15);
    12, (23/2), (7/2), (-16/3);
    (60/7), (-141/14), (-57/14), (160/21);
    (264/7), (-255/14), (-129/14), (368/21);
    (-48), 15, 21, (-16);
    (288/5), (-78/5), (66/5), (152/15);
    (-32), 28, 36, (-160/3);
    (-96), 55, 77, (-376/3);
    (144/5), (-54/5), (18/5), (-224/15);
    36, 18, (-6), (-112/3);
    (234/7), (-153/14), (-45/7), (40/7);
    48, 12, 0, (-64/3);
    (-12), (-27), (-30), (208/3);
    36, (-117/2), (-441/10), (492/5);
    (-80), 56, 8, (-128/3);
    0, (-99), (-117), 184;
    30, (-15), (-15), (40/3);
    (-32), 28, 20, (-32);
    20, (85/2), (155/2), (-100)]

theorem f408desc6_step : f413raise*f408desc5=f408desc6 := by
  refine natFourSparseRowProduct_matrix_check f413raise f408desc5 f408desc6
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 0) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 1) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 2) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 3) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 4) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 5) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 6) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 7) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 8) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 9) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 10) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 11) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 12) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 13) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 14) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 15) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 16) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 17) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 18) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 19) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 20) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 21) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 22) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 23) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 24) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 25) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 26) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 27) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 28) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 29) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 30) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 31) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 32) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 33) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 34) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 35) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 36) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 37) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 38) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 39) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 40) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 41) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 42) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 43) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 44) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 45) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f413raiseSparseRows 46) f408desc5 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc6 46 b)
      (by decide +kernel) 0 b

theorem f408desc6_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f408desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f408basis (complexify b408relative *ᵥ x))
    f413basis f414basis f408desc5 f408desc6 f413raise
    f408desc5_actual f413_actual_raise_block f408desc6_step x

#print axioms f408desc6_step
#print axioms f408desc6_actual
end TorusLean.BosonFiniteCertificate
