import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406P15

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

def f406desc10 : Matrix (Fin 64) (Fin 3) ℚ :=
  !![(-1/10), (1/10), (1/10);
    (-12/5), (12/5), (12/5);
    (-9), 8, (23/3);
    (-22), 14, (32/3);
    (-40), 14, (-4/3);
    (-54), 14, (-88/3);
    (-243/5), (168/5), (-257/5);
    (-24), 72, (-52);
    (-9/2), (93/2), (-47/2);
    (-15), 16, (49/3);
    (-84), 82, (250/3);
    (-158), 86, (212/3);
    (-246), (-2), (-284/3);
    (-1392/5), (-158/5), (-4274/15);
    (-126), 180, (-262);
    108, 468, (-96);
    (-81), 64, (223/3);
    (-252), (-40), (44/3);
    (-462), (-320), (-782/3);
    (-540), (-194), (-506/3);
    (-126), 432, 438;
    108, 408, 412;
    (-274), (-224), (-242/3);
    (-1190), (-530), (100/3);
    (-1152), 240, 920;
    (-240), 1176, 1832;
    (-900), 90, 480;
    (-612), 1428, 1640;
    294, 1008, 882;
    (3654/5), (5796/5), (2646/5);
    (-18), 28, 30;
    (-27), 142, (487/3);
    108, (-8), (4/3);
    171, (-330), (-393);
    246, (-404), (-1550/3);
    639, (-84), (-127);
    468, 72, 84;
    432, 48, 120;
    1944, (-856), (-1984/3);
    1410, (-1640), (-3830/3);
    1080, (-1494), (-198);
    2520, (-1080), 1488;
    860, (-680), (-1580/3);
    (-1170), (-870), (-380);
    (-144), (-1440), (-144);
    1176, (-1176), (-224);
    (-900), (-540), (-1200);
    4536, (-4452), (-8204);
    (8316/5), (-6216/5), (-12516/5);
    756, (-80), (-76);
    2520, 40, (-1160/3);
    (-135), 720, 435;
    (-648), (-216), 1248;
    252, (-672), 700;
    (-1170), 3240, 1410;
    (-10080), 7800, 4280;
    (-3528), (-1176), (-560);
    (-1890), 0, (-2310);
    4158, (-5040), (-7014);
    (-3120), 3360, 2000;
    (-6300), 5880, 4900;
    756, (-504), 756;
    7560, (-2520), 2520;
    1575, (-525), 525]

theorem f406desc10_step : f415raise*f406desc9=f406desc10 := by
  refine natFourSparseRowProduct_matrix_check f415raise f406desc9 f406desc10
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 0) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 1) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 2) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 3) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 4) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 5) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 6) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 7) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 8) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 9) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 10) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 11) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 12) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 13) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 14) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 15) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 16) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 17) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 18) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 19) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 20) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 21) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 22) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 23) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 24) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 25) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 26) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 27) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 28) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 29) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 30) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 31) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 32) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 33) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 34) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 35) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 36) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 37) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 38) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 39) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 40) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 41) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 42) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 43) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 44) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 45) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 46) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 47) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 48) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 49) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 50) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 51) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 52) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 53) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 54) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 55) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 56) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 57) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 58) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 59) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 60) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 61) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 62) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 3) => natFourSparseRowProduct (f415raiseSparseRows 63) f406desc9 b)
      (fun (_ : Fin 1) (b : Fin 3) => f406desc10 63 b)
      (by decide +kernel) 0 b

theorem f406desc10_actual (x : Fin 3 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f406desc10 *ᵥ x) := by
  exact natFour_descendant_step 9
    (fun x => natFourWordBlock f406basis (complexify b406relative *ᵥ x))
    f415basis f416basis f406desc9 f406desc10 f415raise
    f406desc9_actual f415_actual_raise_block f406desc10_step x

#print axioms f406desc10_step
#print axioms f406desc10_actual
end TorusLean.BosonFiniteCertificate
