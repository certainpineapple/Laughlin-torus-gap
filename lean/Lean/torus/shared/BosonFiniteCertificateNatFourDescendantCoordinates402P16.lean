import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402P15

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

def f402desc14 : Matrix (Fin 64) (Fin 1) ℚ :=
  !![(-1);
    (-40);
    (-248);
    (-952);
    (-2548);
    (-5096);
    (-8008);
    (-10296);
    (-5577);
    (-488);
    (-5488);
    (-18928);
    (-45136);
    (-80080);
    (-112112);
    (-130416);
    (-13832);
    (-84448);
    (-176176);
    (-272272);
    (-336336);
    (-178464);
    (-112112);
    (-400400);
    (-528528);
    (-576576);
    (-300300);
    (-672672);
    (-336336);
    (-336336);
    (-1792);
    (-26936);
    (-81536);
    (-168168);
    (-256256);
    (-312312);
    (-164736);
    (-117936);
    (-608608);
    (-1041040);
    (-1297296);
    (-1345344);
    (-640640);
    (-1681680);
    (-1537536);
    (-672672);
    (-720720);
    (-672672);
    0;
    (-144144);
    (-880880);
    (-1081080);
    (-864864);
    (-336336);
    (-1201200);
    (-960960);
    1345344;
    1681680;
    3027024;
    0;
    3363360;
    2690688;
    8408400;
    1051050]

theorem f402desc14_step : f415raise*f402desc13=f402desc14 := by
  ext a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 13 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 14 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 15 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 16 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 17 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 18 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 19 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 20 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 21 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 22 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 23 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 24 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 25 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 26 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 27 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 28 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 29 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 30 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 31 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 32 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 33 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 34 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 35 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 36 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 37 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 38 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 39 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 40 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 41 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 42 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 43 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 44 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 45 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 46 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 47 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 48 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 49 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 50 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 51 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 52 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 53 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 54 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 55 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 56 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 57 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 58 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 59 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 60 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 61 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 62 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f402desc13) 63 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc14 63 b)
      (by decide +kernel) 0 b

theorem f402desc14_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f402desc14 *ᵥ x) := by
  exact natFour_descendant_step 13
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f415basis f416basis f402desc13 f402desc14 f415raise
    f402desc13_actual f415_actual_raise_block f402desc14_step x

#print axioms f402desc14_step
#print axioms f402desc14_actual
end TorusLean.BosonFiniteCertificate
