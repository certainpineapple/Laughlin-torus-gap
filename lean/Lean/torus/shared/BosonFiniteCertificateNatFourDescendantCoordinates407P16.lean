import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407P15

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

def f407desc9 : Matrix (Fin 64) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    1, (-4/3);
    (27/10), (-49/15);
    (19/5), (-12/5);
    (16/5), (22/5);
    (9/5), (164/15);
    (-11/10), (97/15);
    (-33/5), (-36/5);
    (-99/20), (-37/5);
    (51/10), (-107/15);
    (87/5), (-358/15);
    8, 4;
    (-12/5), (908/15);
    (33/5), (998/15);
    (-11/5), (-106/15);
    (-198/5), (-416/5);
    (-9/10), (-77/15);
    (-306/5), (884/15);
    (-327/5), (1178/15);
    (-27), (14/3);
    (-459/5), (-138/5);
    (-414/5), (-28/5);
    (-349/5), (102/5);
    (-92), (-124);
    (-90), (-80);
    (-1236/5), (1208/5);
    (-18), (-106);
    (-72), 328;
    (-357/5), (1946/5);
    (63/5), (2646/5);
    (27/5), (-46/5);
    (9/10), (-91/5);
    (-162/5), (276/5);
    (243/10), (423/5);
    (687/5), (-98/15);
    (1233/10), (-467/5);
    (162/5), (-276/5);
    (-432/5), (276/5);
    (-936/5), (888/5);
    327, (-590/3);
    (2781/5), (-1638/5);
    72, 160;
    94, (-236);
    792, (-1284);
    (1944/5), (-3312/5);
    (-504/5), (392/5);
    486, (-960);
    (3906/5), (-7868/5);
    (1134/5), (-1932/5);
    (-378/5), (284/5);
    0, (-4/3);
    (621/2), (-117);
    (-1296/5), (3528/5);
    (-2142/5), (3556/5);
    171, (-138);
    (-540), 744;
    (-11592/5), (13216/5);
    (-441), (-14);
    (-567/5), (-3654/5);
    (-216), 368;
    (-882), 1372;
    (-1134/5), (1932/5);
    1890, (-1680);
    (945/2), (-420)]

theorem f407desc9_step : f415raise*f407desc8=f407desc9 := by
  refine natFourSparseRowProduct_matrix_check f415raise f407desc8 f407desc9
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 0) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 1) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 2) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 3) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 4) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 5) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 6) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 7) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 8) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 9) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 10) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 11) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 12) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 13) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 14) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 15) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 16) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 17) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 18) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 19) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 20) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 21) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 22) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 23) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 24) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 25) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 26) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 27) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 28) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 29) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 30) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 31) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 32) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 33) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 34) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 35) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 36) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 37) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 38) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 39) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 40) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 41) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 42) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 43) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 44) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 45) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 46) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 47) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 48) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 49) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 50) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 51) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 52) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 53) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 54) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 55) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 56) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 57) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 58) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 59) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 60) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 61) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 62) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 63) f407desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc9 63 b)
      (by decide +kernel) 0 b

theorem f407desc9_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f407desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f415basis f416basis f407desc8 f407desc9 f415raise
    f407desc8_actual f415_actual_raise_block f407desc9_step x

#print axioms f407desc9_step
#print axioms f407desc9_actual
end TorusLean.BosonFiniteCertificate
