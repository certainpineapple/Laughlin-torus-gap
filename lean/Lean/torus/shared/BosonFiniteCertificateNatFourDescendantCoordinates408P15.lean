import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408P14

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

def f408desc7 : Matrix (Fin 54) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (13/35), (-13/35), (-13/35), (13/21);
    1, (-1/2), (-2/5), (3/5);
    (11/5), (-1/5), (1/2), (-17/15);
    (13/5), (-3/5), (3/2), (-41/15);
    (3/5), (-21/10), (7/5), (-1);
    (-3/5), (-12/5), (6/5), (13/5);
    (37/35), (-37/35), (61/35), (479/105);
    (2/5), (-9/10), (-1), (26/15);
    (2/5), (11/10), (1/2), (-14/15);
    (24/5), (26/5), (26/5), (-32/3);
    (-2/5), (-1/10), (13/10), (-94/15);
    (-84/5), (-31/5), (-34/5), (116/15);
    (-22/5), (17/5), (-19/5), (62/15);
    (264/35), (226/35), (6/7), (-248/105);
    (18/5), (27/5), (27/10), (-68/15);
    (164/5), (56/5), (-3/5), (8/15);
    14, (-13/2), (-35/2), (74/3);
    (-66/5), (-84/5), (-87/5), (22/5);
    (168/5), (-58/5), (-8/5), (-152/3);
    28, 1, (-7), (56/3);
    (-22), (-10), (-3), (86/3);
    (-144/5), (-116/5), (52/5), (-416/15);
    (84/5), (-84/5), (21/5), (-28);
    (-42), 2, 9, (32/3);
    (84/5), (21/5), (-161/5), (448/5);
    (84/5), (21/5), (-84/5), (112/3);
    (-18/5), (1/10), 0, (2/5);
    (-132/5), (27/5), 6, (-116/15);
    (-116/5), (11/5), (14/5), (-76/15);
    (-42), (-7/2), (-12), (50/3);
    (-234/5), (153/10), (-51/5), 14;
    (104/5), (226/5), 8, (-248/15);
    (-18), (-3), (33/10), (-28/15);
    56, (-42), (-28), (152/3);
    (-66), (-15/2), (-21/2), (106/3);
    (-48/5), (108/5), (168/5), (-64/3);
    (476/5), (14/5), 21, (-84/5);
    12, 9, 25, (-80/3);
    (-240), 124, 180, (-752/3);
    (112/5), (28/5), (504/5), (-784/5);
    (-70), 77, 70, (-448/3);
    (588/5), (147/5), (-126/5), (-784/15);
    42, (-21), (-21/2), (40/3);
    186, (-39), (-57/2), (40/3);
    (-12), 0, (-9), 32;
    (588/5), (-798/5), (-105), (4144/15);
    (-16), 108, 44, (-416/3);
    (-280), 14, (-84), 112;
    (504/5), (-1134/5), (-1008/5), (5488/15);
    126, (-126), (-168), (560/3);
    (-112), 84, 28, (-224/3);
    (-56), 70, 98, (-112);
    70, 70, 140, (-560/3)]

theorem f408desc7_step : f414raise*f408desc6=f408desc7 := by
  refine natFourSparseRowProduct_matrix_check f414raise f408desc6 f408desc7
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 0) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 1) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 2) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 3) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 4) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 5) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 6) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 7) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 8) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 9) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 10) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 11) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 12) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 13) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 14) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 15) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 16) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 17) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 18) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 19) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 20) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 21) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 22) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 23) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 24) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 25) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 26) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 27) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 28) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 29) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 30) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 31) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 32) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 33) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 34) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 35) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 36) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 37) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 38) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 39) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 40) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 41) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 42) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 43) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 44) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 45) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 46) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 47) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 48) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 49) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 50) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 51) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 52) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 53) f408desc6 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc7 53 b)
      (by decide +kernel) 0 b

theorem f408desc7_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f408desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f408basis (complexify b408relative *ᵥ x))
    f414basis f415basis f408desc6 f408desc7 f414raise
    f408desc6_actual f414_actual_raise_block f408desc7_step x

#print axioms f408desc7_step
#print axioms f408desc7_actual
end TorusLean.BosonFiniteCertificate
