import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406P13

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

def f406desc8 : Matrix (Fin 47) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-9/5), (9/5), (9/5);
    (-51/10), (41/10), (113/30);
    (-10), 4, (4/3);
    (-149/10), (19/10), (-233/30);
    (-71/5), (31/5), (-227/15);
    (-53/10), (193/10), (-401/30);
    (2/5), (68/5), (-76/15);
    (-36/5), (41/5), (128/15);
    (-24), 22, (70/3);
    (-176/5), (-34/5), (-202/15);
    (-52), (-34), (-196/3);
    (-114/5), (54/5), (-246/5);
    (248/5), (452/5), (236/15);
    (-42/5), (-23/5), (46/15);
    (-56), (-82), (-130/3);
    (-129), (-69), (-7);
    (-48), 60, 148;
    28, 70, (364/3);
    (-110), (-44), (40/3);
    (-272), 64, (568/3);
    (-56/5), (1036/5), (4228/15);
    (-7), 119, (245/3);
    (756/5), (714/5), (84/5);
    0, 8, (28/3);
    (336/5), (4/5), (142/15);
    112, (-72), (-68);
    84, (-109), (-280/3);
    144, (-80), (-8/3);
    112, (-28), (98/3);
    252, (-60), (-50);
    336, (-130), (-394/3);
    (-24), (-132), 28;
    (1512/5), (-1792/5), (1904/15);
    (-208), 96, 32;
    (-224), (-196), (-1204/3);
    (1344/5), (-1904/5), (-7112/15);
    546, (-574), (-3094/3);
    126, 43, 2;
    (-336), 568, (880/3);
    (-504), 266, (728/3);
    (-252/5), (-588/5), (42/5);
    (-1064), 952, (1624/3);
    (-168), (-140), (-644/3);
    315, (-245), (-665/3);
    (-112), 224, (896/3);
    630, (-140), (1120/3)]

theorem f406desc8_step : f413raise*f406desc7=f406desc8 := by
  refine natFourSparseRowProduct_matrix_check f413raise f406desc7 f406desc8
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 0) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 1) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 2) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 3) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 4) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 5) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 6) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 7) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 8) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 9) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 10) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 11) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 12) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 13) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 14) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 15) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 16) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 17) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 18) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 19) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 20) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 21) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 22) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 23) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 24) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 25) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 26) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 27) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 28) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 29) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 30) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 31) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 32) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 33) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 34) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 35) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 36) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 37) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 38) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 39) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 40) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 41) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 42) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 43) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 44) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 45) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f413raiseSparseRows 46) f406desc7 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc8 46 b)
      (by decide +kernel) 0 b

theorem f406desc8_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f406desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f413basis f414basis f406desc7 f406desc8 f413raise
    f406desc7_actual f413_actual_raise_block f406desc8_step x

#print axioms f406desc8_step
#print axioms f406desc8_actual
end TorusLean.BosonFiniteCertificate
