import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406P14

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

def f406desc9 : Matrix (Fin 54) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-21/10), (21/10), (21/10);
    (-69/10), (59/10), (167/30);
    (-151/10), (81/10), (51/10);
    (-249/10), (59/10), (-193/30);
    (-291/10), (81/10), (-229/10);
    (-39/2), (51/2), (-57/2);
    (-9/2), (93/2), (-47/2);
    (-54/5), (59/5), (182/15);
    (-243/5), (233/5), (719/15);
    (-396/5), (116/5), (188/15);
    (-117), (-37), (-283/3);
    (-516/5), (-54/5), (-724/5);
    (81/5), (699/5), (-301/5);
    (252/5), (588/5), (28/5);
    (-162/5), (87/5), (132/5);
    (-108), (-98), (-152/3);
    (-237), (-185), (-347/3);
    (-999/5), (9/5), (459/5);
    (288/5), (1452/5), (2032/5);
    (-166), (-126), (-30);
    (-621), (-93), 209;
    (-1656/5), (1656/5), (3096/5);
    (84/5), (1386/5), (2016/5);
    (-279), 183, 271;
    (1386/5), (3654/5), (2394/5);
    (756/5), (714/5), (84/5);
    (-36/5), (81/5), (268/15);
    (216/5), (234/5), (304/5);
    144, (-78), (-72);
    144, (-215), (-680/3);
    (1026/5), (-891/5), (-726/5);
    (2088/5), (-228/5), (392/5);
    378, (-63), (-28);
    1008, (-476), (-1232/3);
    351, (-549), (-297);
    (2592/5), (-2952/5), (1488/5);
    (2772/5), (-1722/5), (1568/5);
    18, (-78), (-86);
    (-936), (-72), (-120);
    (3024/5), (-5544/5), (-4704/5);
    315, (-651), (-1351);
    1512, (-1386), (-2520);
    378, (-17), (-48);
    378, 567, 168;
    (-864), 702, 564;
    (-1512/5), (-1638/5), (1932/5);
    (-1944), 2184, 1160;
    (-3528), 2100, 952;
    0, (-756), (-672);
    1323, (-1449), (-1911);
    (-1176), 1176, 840;
    756, 252, 1428;
    1575, (-525), 525]

theorem f406desc9_step : f414raise*f406desc8=f406desc9 := by
  refine natFourSparseRowProduct_matrix_check f414raise f406desc8 f406desc9
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 0) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 1) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 2) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 3) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 4) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 5) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 6) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 7) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 8) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 9) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 10) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 11) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 12) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 13) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 14) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 15) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 16) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 17) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 18) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 19) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 20) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 21) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 22) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 23) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 24) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 25) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 26) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 27) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 28) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 29) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 30) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 31) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 32) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 33) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 34) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 35) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 36) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 37) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 38) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 39) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 40) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 41) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 42) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 43) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 44) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 45) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 46) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 47) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 48) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 49) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 50) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 51) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 52) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f414raiseSparseRows 53) f406desc8 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc9 53 b)
      (by decide +kernel) 0 b

theorem f406desc9_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f406desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f414basis f415basis f406desc8 f406desc9 f414raise
    f406desc8_actual f414_actual_raise_block f406desc9_step x

#print axioms f406desc9_step
#print axioms f406desc9_actual
end TorusLean.BosonFiniteCertificate
