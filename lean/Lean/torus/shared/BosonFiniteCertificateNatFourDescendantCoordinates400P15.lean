import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400P14

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

def f400desc15 : Matrix (Fin 54) (Fin 1) ℚ :=
  !![4;
    180;
    1260;
    5460;
    16380;
    36036;
    60060;
    77220;
    2520;
    32760;
    131040;
    360360;
    720720;
    1081080;
    617760;
    98280;
    720720;
    1801800;
    3243240;
    4324320;
    1201200;
    5405400;
    8648640;
    5045040;
    5405400;
    15135120;
    3027024;
    10920;
    196560;
    720720;
    1801800;
    3243240;
    4324320;
    1081080;
    7207200;
    16216200;
    25945920;
    15135120;
    10810800;
    43243200;
    60540480;
    37837800;
    45405360;
    1801800;
    16216200;
    32432400;
    45405360;
    43243200;
    151351200;
    90810720;
    113513400;
    33633600;
    151351200;
    63063000]

theorem f400desc15_step : f414raise*f400desc14=f400desc15 := by
  ext a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 13 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 14 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 15 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 16 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 17 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 18 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 19 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 20 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 21 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 22 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 23 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 24 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 25 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 26 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 27 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 28 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 29 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 30 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 31 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 32 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 33 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 34 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 35 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 36 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 37 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 38 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 39 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 40 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 41 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 42 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 43 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 44 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 45 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 46 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 47 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 48 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 49 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 50 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 51 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 52 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f414raise*f400desc14) 53 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc15 53 b)
      (by decide +kernel) 0 b

theorem f400desc15_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[15]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f400desc15 *ᵥ x) := by
  exact natFour_descendant_step 14
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f414basis f415basis f400desc14 f400desc15 f414raise
    f400desc14_actual f414_actual_raise_block f400desc15_step x

#print axioms f400desc15_step
#print axioms f400desc15_actual
end TorusLean.BosonFiniteCertificate
