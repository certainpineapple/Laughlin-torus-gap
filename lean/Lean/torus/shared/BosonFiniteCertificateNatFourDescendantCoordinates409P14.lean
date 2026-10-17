import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409P13

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

def f409desc5 : Matrix (Fin 47) (Fin 3) ℚ :=
  !![(-1/70), (1/56), (1/56);
    (-3/35), (3/28), (3/28);
    (-1/14), (-3/280), (-31/280);
    (-6/35), (9/140), (-47/140);
    (1/70), (27/56), (-1/56);
    (19/35), (9/28), (9/28);
    (1/10), (-21/40), (3/40);
    (-2/7), (-69/140), (-13/140);
    (1/5), (-3/20), (-1/20);
    (4/5), (-27/20), (-19/20);
    (-36/35), (-9/140), (47/140);
    (2/7), (9/14), (23/14);
    (78/35), (-27/70), (1/70);
    (-88/35), (87/70), (-81/70);
    (1/7), (-81/140), (73/140);
    (-4/7), (27/28), (83/28);
    (33/7), (-81/28), (-53/28);
    (24/7), (-81/14), (-25/14);
    (-6/5), (-21/10), (13/10);
    (2/7), (81/28), (-31/28);
    (-8/7), (45/7), (-39/7);
    (-24/5), (-9/10), (47/10);
    (-1), (9/4), (-7/4);
    (18/5), (-9/2), (-3/2);
    (4/7), (-3/14), (-3/14);
    (-2/7), (45/28), (17/28);
    (-36/7), (27/14), (27/14);
    (-11/7), (-99/28), (-57/28);
    (-8/35), (171/35), (-53/35);
    (-2), (33/4), (5/4);
    (-18/7), (153/28), (69/28);
    (-4/7), (-225/28), (-169/28);
    8, (-45/2), (-21/2);
    (24/5), (27/5), (59/5);
    (-48/7), (18/7), (18/7);
    (-24), (45/2), (53/2);
    (-8/5), (27/5), (59/5);
    14, (-9/2), (-13/2);
    (39/7), (-27/28), (-69/28);
    (136/7), (-72/7), (-44/7);
    6, (-27/2), (-17/2);
    6, (-243/20), (-231/20);
    (-24), 36, 28;
    (-8), (-27/2), (-83/2);
    15, (-75/4), (-95/4);
    (-16), 22, 22;
    10, (-15/4), (65/4)]

theorem f409desc5_step : f413raise*f409desc4=f409desc5 := by
  refine natFourSparseRowProduct_matrix_check f413raise f409desc4 f409desc5
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 0) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 1) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 2) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 3) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 4) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 5) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 6) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 7) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 8) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 9) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 10) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 11) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 12) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 13) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 14) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 15) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 16) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 17) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 18) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 19) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 20) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 21) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 22) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 23) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 24) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 25) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 26) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 27) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 28) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 29) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 30) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 31) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 32) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 33) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 34) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 35) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 36) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 37) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 38) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 39) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 40) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 41) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 42) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 43) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 44) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 45) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 46) f409desc4 b)
      (fun (_ : Fin 1) (b : Fin 3) => f409desc5 46 b)
      (by decide +kernel) 0 b

theorem f409desc5_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f409desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f409basis (complexify b409relative *ᵥ x))
    f413basis f414basis f409desc4 f409desc5 f413raise
    f409desc4_actual f413_actual_raise_block f409desc5_step x

#print axioms f409desc5_step
#print axioms f409desc5_actual
end TorusLean.BosonFiniteCertificate
