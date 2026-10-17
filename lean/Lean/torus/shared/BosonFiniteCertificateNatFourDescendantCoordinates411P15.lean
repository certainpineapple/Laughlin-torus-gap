import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates411P14

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

def f411desc4 : Matrix (Fin 54) (Fin 4) ℚ :=
  !![(1/252), (-1/210), (-1/210), (1/120);
    (1/252), (-1/210), (-1/210), (1/120);
    (1/28), (1/70), (3/70), (-29/280);
    (11/252), (-17/210), (1/210), (-37/840);
    (-41/252), (-19/210), (-1/30), (127/840);
    (-1/84), (1/10), (3/70), (23/280);
    (65/252), (5/42), (1/30), (-61/840);
    (-5/28), (-3/70), (-1/14), (-13/280);
    (-8/63), (2/21), (1/15), (-37/420);
    (13/126), (2/15), (-4/105), (37/420);
    (8/63), (-4/105), (-8/21), (64/105);
    (-95/126), (44/105), (8/105), (-143/420);
    (62/63), (-4/105), (2/15), (-169/210);
    (9/14), (-19/35), (-1/35), (33/140);
    (-6/7), (-4/35), (4/35), (13/35);
    (3/14), (-3/35), (-1/5), (18/35);
    (-5/7), (-6/35), (18/35), (-24/35);
    (-155/126), (-4/105), (32/105), (-599/420);
    (9/14), (9/35), (-43/35), (159/140);
    (-4/7), (12/5), (16/35), (1/7);
    (40/63), (-16/21), (46/105), (-2/3);
    (65/42), (3/35), (-33/35), (333/140);
    (4/21), (-52/35), (-4/35), (22/35);
    (2/3), (-14/5), (4/5), (-17/10);
    (-15/7), (107/35), (4/5), (11/70);
    (-2/3), 0, (2/5), (-9/5);
    1, 0, (-4/5), (3/5);
    (-1/9), (-2/21), (-1/105), (13/420);
    (2/3), (-4/5), (-2/5), (1/2);
    (40/63), (88/105), (46/105), (-23/30);
    0, (6/35), (23/35), (-15/28);
    1, (-18/7), (-23/35), (201/140);
    (-4/7), (4/35), (8/35), (-5/7);
    (-25/42), (19/35), (23/35), (-46/35);
    (-40/63), (44/15), (128/105), (-149/105);
    (-5/2), (-18/7), (-86/35), (183/28);
    (-16/7), (12/7), (-4/5), (18/35);
    2, (22/5), (4/5), (-39/10);
    (50/7), (-76/35), (-118/35), (19/5);
    (-80/21), (12/5), (12/7), (-228/35);
    4, (-68/5), (-4), 4;
    (-25/3), (37/5), (26/5), (-13/2);
    5, 0, (-16/5), (57/5);
    (-5/2), (3/5), (1/5), (-3/10);
    (25/14), (-159/35), (-117/35), (57/10);
    (-45/7), (114/35), (218/35), (-237/35);
    3, (18/5), 2, (3/5);
    (200/21), (-8/5), (32/35), (-172/35);
    (-50/3), 12, 12, (-102/5);
    10, (-84/5), (-68/5), (114/5);
    0, (33/5), (34/5), (-231/10);
    0, (8/5), (-16/5), (36/5);
    0, (-44/5), (-72/5), (154/5);
    0, 5, 10, (-35/2)]

theorem f411desc4_step : f414raise*f411desc3=f411desc4 := by
  refine natFourSparseRowProduct_matrix_check f414raise f411desc3 f411desc4
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 0) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 1) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 2) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 3) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 4) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 5) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 6) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 7) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 8) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 9) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 10) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 11) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 12) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 13) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 14) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 15) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 16) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 17) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 18) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 19) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 20) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 21) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 22) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 23) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 24) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 25) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 26) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 27) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 28) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 29) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 30) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 31) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 32) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 33) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 34) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 35) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 36) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 37) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 38) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 39) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 40) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 41) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 42) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 43) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 44) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 45) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 46) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 47) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 48) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 49) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 50) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 51) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 52) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f414raiseSparseRows 53) f411desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f411desc4 53 b)
      (by decide +kernel) 0 b

theorem f411desc4_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f411basis (complexify b411relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f411desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f411basis (complexify b411relative *ᵥ x))
    f414basis f415basis f411desc3 f411desc4 f414raise
    f411desc3_actual f414_actual_raise_block f411desc4_step x

#print axioms f411desc4_step
#print axioms f411desc4_actual
end TorusLean.BosonFiniteCertificate
