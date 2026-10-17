import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402P13

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

def f402desc12 : Matrix (Fin 47) (Fin 1) ℚ :=
  !![(-1);
    (-34);
    (-177);
    (-564);
    (-1243);
    (-2046);
    (-2673);
    (-1452);
    (-346);
    (-3192);
    (-8888);
    (-16940);
    (-24156);
    (-27984);
    (-6402);
    (-30360);
    (-48510);
    (-58608);
    (-30492);
    (-29700);
    (-76560);
    (-77616);
    (-39270);
    (-36036);
    (-1032);
    (-12276);
    (-28600);
    (-44550);
    (-52272);
    (-26796);
    (-40260);
    (-146520);
    (-166320);
    (-144144);
    (-89760);
    (-92400);
    (-11088);
    41580;
    (-32670);
    (-102960);
    (-13860);
    24948;
    55440;
    609840;
    173250;
    184800;
    438900]

theorem f402desc12_step : f413raise*f402desc11=f402desc12 := by
  ext a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 13 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 14 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 15 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 16 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 17 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 18 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 19 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 20 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 21 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 22 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 23 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 24 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 25 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 26 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 27 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 28 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 29 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 30 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 31 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 32 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 33 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 34 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 35 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 36 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 37 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 38 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 39 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 40 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 41 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 42 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 43 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 44 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 45 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f402desc11) 46 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc12 46 b)
      (by decide +kernel) 0 b

theorem f402desc12_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f402desc12 *ᵥ x) := by
  exact natFour_descendant_step 11
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f413basis f414basis f402desc11 f402desc12 f413raise
    f402desc11_actual f413_actual_raise_block f402desc12_step x

#print axioms f402desc12_step
#print axioms f402desc12_actual
end TorusLean.BosonFiniteCertificate
