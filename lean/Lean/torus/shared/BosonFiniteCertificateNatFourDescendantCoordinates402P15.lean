import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402P14

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

def f402desc13 : Matrix (Fin 54) (Fin 1) ℚ :=
  !![(-1);
    (-37);
    (-211);
    (-741);
    (-1807);
    (-3289);
    (-4719);
    (-5577);
    (-414);
    (-4238);
    (-13208);
    (-28314);
    (-45188);
    (-57486);
    (-30888);
    (-9594);
    (-52052);
    (-95810);
    (-131274);
    (-147576);
    (-60060);
    (-184470);
    (-212784);
    (-108108);
    (-115830);
    (-228228);
    (-36036);
    (-1378);
    (-18564);
    (-49764);
    (-90090);
    (-120978);
    (-133848);
    (-71214);
    (-314600);
    (-450450);
    (-473616);
    (-228228);
    (-265980);
    (-514800);
    (-336336);
    (-90090);
    36036;
    (-72930);
    (-347490);
    (-283140);
    (-108108);
    (-240240);
    600600;
    648648;
    1171170;
    240240;
    2042040;
    1051050]

theorem f402desc13_step : f414raise*f402desc12=f402desc13 := by
  ext a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 13 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 14 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 15 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 16 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 17 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 18 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 19 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 20 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 21 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 22 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 23 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 24 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 25 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 26 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 27 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 28 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 29 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 30 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 31 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 32 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 33 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 34 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 35 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 36 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 37 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 38 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 39 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 40 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 41 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 42 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 43 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 44 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 45 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 46 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 47 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 48 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 49 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 50 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 51 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 52 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f402desc12) 53 b)
      (fun (_ : Fin 1) (b : Fin 1) => f402desc13 53 b)
      (by decide +kernel) 0 b

theorem f402desc13_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f402desc13 *ᵥ x) := by
  exact natFour_descendant_step 12
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f414basis f415basis f402desc12 f402desc13 f414raise
    f402desc12_actual f414_actual_raise_block f402desc13_step x

#print axioms f402desc13_step
#print axioms f402desc13_actual
end TorusLean.BosonFiniteCertificate
