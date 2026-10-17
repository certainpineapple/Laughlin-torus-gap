import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates412P14

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

def f412desc3 : Matrix (Fin 54) (Fin 7) ℚ :=
  !![(1/462), (-1/462), (1/330), (-1/462), (1/330), (1/330), (-1/165);
    (-1/154), (1/154), (-1/110), (1/154), (-1/110), (-1/110), (1/55);
    (13/154), (-1/77), (3/770), (-1/198), (-23/1155), (-193/6930), (7/110);
    (-5/42), (-1/42), (13/210), 0, (1/30), (1/42), (-11/210);
    (1/22), (23/462), (-17/770), (17/231), (1/154), (59/2310), (-13/154);
    (3/14), (-1/42), (-1/14), (-1/63), (-11/210), (-11/630), (3/70);
    (-17/42), (-2/21), (1/30), (-2/21), (-1/105), (1/210), (1/21);
    (3/14), (1/14), (3/70), (1/14), (1/70), (1/70), 0;
    (-9/77), (1/22), (-19/385), (26/693), (-59/2310), (-61/3465), (3/110);
    (3/7), (-1/14), (1/35), (-19/126), (29/210), (11/63), (-12/35);
    (-104/77), (26/231), (-68/385), (-6/77), (-2/385), (16/1155), (4/385);
    (11/7), (1/7), (-1/7), (-4/63), (-16/105), (-13/45), (23/35);
    (-2/7), (-1/21), (2/5), (-8/63), (31/105), (2/63), (-1/7);
    (-15/7), (1/14), (-3/35), (1/14), (11/70), (1/35), (-3/7);
    (12/7), 0, (-12/35), 0, (-4/35), (-4/35), 0;
    (54/77), (1/77), (3/77), (61/462), (-1/55), (-2/231), (-27/770);
    (-12/7), (-1/21), (2/7), (4/9), (-1/3), (-152/315), (33/35);
    (25/7), (-20/21), (1/7), (-20/63), (37/105), (29/63), (-23/35);
    (-27/7), (3/14), (-27/35), (15/14), (-3/14), (11/35), (-18/35);
    (12/7), (-2/7), (12/7), (-4/7), (-2/7), (-4/35), (24/35);
    (-20/21), (5/21), (22/105), (-5/7), (5/21), (32/105), (-13/21);
    (15/7), (20/21), (-9/7), (-10/21), (-8/35), (1/5), (-3/5);
    (-24/7), (22/21), (-72/35), (26/21), (-18/35), (-16/21), (54/35);
    2, 0, (-2/5), (-1), (4/5), (2/5), (-2/5);
    0, (-10/7), (87/35), (5/7), (2/35), (-22/35), (6/7);
    0, (-1), (6/5), (-1/3), (3/5), (8/15), (-6/5);
    0, 1, (-6/5), 0, (-3/5), 0, 0;
    (-1/7), (-1/14), (1/7), (-1/63), (13/210), (11/315), (-1/14);
    (6/11), (-9/77), (6/77), (-16/231), (-5/77), (-26/231), (3/11);
    (-2), (1/7), (-22/35), (16/63), (-53/105), (-86/315), (19/35);
    (25/7), (-5/14), (37/35), (-5/21), (19/70), (11/21), (-79/70);
    (-27/7), (15/14), (9/35), (4/7), (-9/70), (1/7), (-9/70);
    (12/7), (-4/7), (-36/35), (-2/7), (-8/35), (4/35), (36/35);
    (6/7), (6/7), (-33/35), (19/42), (-16/35), (-46/105), (57/70);
    (-20/7), (-10/7), (44/35), (-20/63), (226/105), (116/63), (-4);
    (45/7), (-15/14), (-27/35), (-15/14), (-3/70), (-5/7), (36/35);
    (-72/7), (18/7), (-72/35), (10/7), (-66/35), (-96/35), (18/5);
    6, (-2), (18/5), (-1), 2, (6/5), (-18/5);
    0, (25/21), (-6/35), (25/21), (-1/35), (-4/7), (51/35);
    0, (10/7), (-24/35), (10/21), (-18/7), (-40/21), (186/35);
    0, (2/3), (-24/5), (2/3), (-6/5), (8/5), (-6);
    0, (-5), (39/5), (-10/3), (19/5), (10/3), (-24/5);
    0, 3, (-18/5), 2, (-9/5), (-16/5), (36/5);
    0, 0, (3/5), (-5/6), (2/5), (8/15), (-9/10);
    0, (-10/7), (9/7), (-5/14), (-36/35), (-32/35), (153/70);
    0, 0, (-18/5), (-15/7), (-24/35), (-32/35), (99/35);
    0, 0, (18/5), 1, (12/5), (8/5), (-9/5);
    0, (80/21), (-24/7), (40/7), (-104/35), (-32/15), (96/35);
    0, (-20/3), (36/5), (-10), (56/5), (40/3), (-126/5);
    0, 4, (-36/5), 6, (-48/5), (-8), 18;
    0, 0, (9/5), 0, (12/5), (6/5), (-36/5);
    0, 0, (8/5), 0, (8/5), 0, (-8/5);
    0, 0, (-12/5), 0, (-36/5), (-48/5), (108/5);
    0, 0, 1, 0, 4, 6, (-12)]

theorem f412desc3_step : f414raise*f412desc2=f412desc3 := by
  refine natFourSparseRowProduct_matrix_check f414raise f412desc2 f412desc3
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 0) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 1) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 2) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 3) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 4) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 5) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 6) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 7) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 8) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 9) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 10) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 11) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 12) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 13) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 14) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 15) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 16) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 17) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 18) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 19) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 20) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 21) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 22) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 23) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 24) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 25) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 26) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 27) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 28) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 29) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 30) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 31) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 32) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 33) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 34) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 35) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 36) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 37) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 38) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 39) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 40) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 41) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 42) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 43) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 44) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 45) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 46) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 47) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 48) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 49) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 50) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 51) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 52) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f414raiseSparseRows 53) f412desc2 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc3 53 b)
      (by decide +kernel) 0 b

theorem f412desc3_actual (x : Fin 7 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f412basis (complexify b412relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f412desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f412basis (complexify b412relative *ᵥ x))
    f414basis f415basis f412desc2 f412desc3 f414raise
    f412desc2_actual f414_actual_raise_block f412desc3_step x

#print axioms f412desc3_step
#print axioms f412desc3_actual
end TorusLean.BosonFiniteCertificate
