import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409P15

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

def f409desc7 : Matrix (Fin 64) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (-6/35), (3/14), (3/14);
    (-2/7), (9/35), (11/70);
    (-2/5), (3/20), (-9/20);
    (-2/5), (3/5), (-4/5);
    (2/5), (27/20), (-1/20);
    (6/5), (3/5), (7/10);
    (6/35), (-12/7), (2/7);
    (-33/70), (-423/280), (-31/280);
    (-8/35), (27/70), (17/35);
    (4/5), (-27/20), (-19/20);
    0, (-57/20), (-69/20);
    (-8/5), (27/20), (-1/20);
    4, (81/20), (97/20);
    (24/5), (3/10), (21/10);
    (-36/5), (-27/10), (-39/10);
    2, (-18/5), (-17/10);
    0, (-27/5), (11/5);
    (12/5), 0, 9;
    (92/5), (-189/20), (27/20);
    (44/5), (-18), (-5);
    (-32/7), (-297/35), (-59/35);
    (-8/5), (18/5), (31/5);
    8, (63/4), (-13/4);
    12, 0, (-16);
    (-16), (-15), 9;
    2, 18, (-17);
    (-32/5), (117/10), (-191/10);
    (-28/5), (-42/5), (21/5);
    (56/5), (-189/10), (-63/10);
    (4/5), (-3/10), (-1/10);
    (28/5), (-63/20), (-61/20);
    (-24/5), (9/5), (3/5);
    (-68/5), (81/20), (127/20);
    (-12/5), (9/10), (3/10);
    (-32/5), (117/5), (-47/10);
    (-344/35), (801/35), (-53/35);
    (12/5), (27/5), (9/5);
    (-184/5), (153/5), (121/5);
    (-16), (-36), (-11);
    36, (-243/4), (-147/4);
    0, 63, 27;
    (-24), 9, 3;
    (-32), (-99/4), (-103/4);
    (-224/5), 36, 76;
    (-168/5), (273/5), (441/5);
    (-44), (81/2), (53/2);
    (56/5), (567/10), (959/10);
    (168/5), (-63/5), (-21/5);
    0, (63/5), (21/5);
    28, 0, (-14);
    78, (-108), (-135/2);
    72, (-459/5), (-243/5);
    (112/5), (-63/5), (-21/5);
    72, (-27), (-26);
    (-16), 9, 25;
    (-224/5), (-189/5), (-273/5);
    (-28), 0, (-77);
    (672/5), (-189), (-294);
    (-32), 76, 68;
    (-224), 273, 231;
    (-168/5), (63/5), (21/5);
    84, (-63), 21;
    35, (-105/4), (35/4)]

theorem f409desc7_step : f415raise*f409desc6=f409desc7 := by
  refine natFourSparseRowProduct_matrix_check f415raise f409desc6 f409desc7
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 0) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 1) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 2) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 3) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 4) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 5) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 6) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 7) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 8) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 9) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 10) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 11) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 12) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 13) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 14) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 15) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 16) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 17) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 18) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 19) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 20) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 21) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 22) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 23) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 24) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 25) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 26) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 27) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 28) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 29) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 30) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 31) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 32) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 33) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 34) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 35) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 36) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 37) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 38) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 39) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 40) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 41) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 42) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 43) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 44) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 45) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 46) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 47) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 48) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 49) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 50) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 51) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 52) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 53) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 54) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 55) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 56) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 57) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 58) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 59) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 60) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 61) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 62) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 63) f409desc6 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc7 63 b)
      (by decide +kernel) 0 b

theorem f409desc7_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f409desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f409basis (complexify b409relative *ᵥ x))
    f415basis f416basis f409desc6 f409desc7 f415raise
    f409desc6_actual f415_actual_raise_block f409desc7_step x

#print axioms f409desc7_step
#print axioms f409desc7_actual
end TorusLean.BosonFiniteCertificate
