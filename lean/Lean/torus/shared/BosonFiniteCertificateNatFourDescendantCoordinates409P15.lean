import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409P14

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

def f409desc6 : Matrix (Fin 54) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (-9/70), (9/56), (9/56);
    (-11/70), (27/280), (-1/280);
    (-17/70), (3/56), (-25/56);
    (-11/70), (153/280), (-99/280);
    (39/70), (45/56), (17/56);
    (9/14), (-57/280), (111/280);
    (-33/70), (-423/280), (-31/280);
    (1/35), (9/140), (23/140);
    (37/35), (-117/70), (-89/70);
    (-4/7), (-9/7), (-9/7);
    (-5/7), (54/35), (68/35);
    (18/5), (9/10), (23/10);
    (-3/35), (-27/140), (-139/140);
    (-108/35), (9/35), (-47/35);
    (33/35), (-27/14), (-3/7);
    (-46/35), (-9/35), (152/35);
    (31/7), (-9/7), (19/7);
    (363/35), (-1269/140), (-513/140);
    (-52/35), (-306/35), (-12/35);
    (-2/7), (27/7), (13/7);
    (29/7), (261/28), (-271/28);
    (-88/35), (-9/35), (-93/35);
    (-6), (-3), 6;
    (-15/7), (243/28), (-205/28);
    (2/5), (-27/5), (-9/5);
    (18/5), (-9/2), (-3/2);
    (27/35), (-51/140), (-37/140);
    (78/35), (-27/70), (-69/70);
    (-226/35), (243/70), (201/70);
    (-45/7), (-27/28), (43/28);
    (3/7), (27/28), (-99/28);
    (-236/35), (792/35), (-6/35);
    (-3), (81/10), (21/5);
    (-116/7), (54/7), (40/7);
    9, (-81/2), (-45/2);
    (552/35), (-459/35), (-123/35);
    (-2/5), (99/5), (78/5);
    (-50/7), (-18/7), (-32/7);
    (-216/7), (81/7), (109/7);
    (-136/5), (189/5), (333/5);
    (-11), (81/4), (73/4);
    30, (-81/10), (-27/10);
    3, (9/2), 0;
    (249/7), (-297/14), (-138/7);
    (234/7), (-324/7), (-177/7);
    (114/5), (-162/5), (-99/5);
    8, 18, 18;
    (-68), 54, 24;
    (12/5), (-162/5), (-264/5);
    51, (-297/4), (-477/4);
    (-40), 58, 50;
    (-36), 45, 57;
    35, (-105/4), (35/4)]

theorem f409desc6_step : f414raise*f409desc5=f409desc6 := by
  refine natFourSparseRowProduct_matrix_check f414raise f409desc5 f409desc6
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 0) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 1) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 2) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 3) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 4) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 5) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 6) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 7) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 8) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 9) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 10) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 11) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 12) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 13) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 14) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 15) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 16) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 17) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 18) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 19) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 20) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 21) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 22) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 23) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 24) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 25) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 26) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 27) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 28) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 29) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 30) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 31) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 32) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 33) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 34) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 35) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 36) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 37) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 38) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 39) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 40) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 41) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 42) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 43) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 44) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 45) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 46) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 47) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 48) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 49) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 50) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 51) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 52) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 53) f409desc5 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc6 53 b)
      (by decide +kernel) 0 b

theorem f409desc6_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f409desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f409basis (complexify b409relative *ᵥ x))
    f414basis f415basis f409desc5 f409desc6 f414raise
    f409desc5_actual f414_actual_raise_block f409desc6_step x

#print axioms f409desc6_step
#print axioms f409desc6_actual
end TorusLean.BosonFiniteCertificate
