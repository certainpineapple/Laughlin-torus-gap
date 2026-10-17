import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400P13

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

def f400desc14 : Matrix (Fin 47) (Fin 1) ℚ :=
  !![4;
    168;
    1092;
    4368;
    12012;
    24024;
    36036;
    20592;
    2184;
    26208;
    96096;
    240240;
    432432;
    576576;
    72072;
    480480;
    1081080;
    1729728;
    1009008;
    720720;
    2882880;
    4036032;
    2522520;
    3027024;
    8736;
    144144;
    480480;
    1081080;
    1729728;
    1009008;
    720720;
    4324320;
    8648640;
    12108096;
    5765760;
    20180160;
    12108096;
    15135120;
    1081080;
    8648640;
    15135120;
    9081072;
    20180160;
    60540480;
    12612600;
    13453440;
    25225200]

theorem f400desc14_step : f413raise*f400desc13=f400desc14 := by
  ext a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 13 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 14 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 15 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 16 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 17 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 18 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 19 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 20 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 21 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 22 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 23 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 24 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 25 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 26 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 27 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 28 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 29 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 30 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 31 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 32 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 33 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 34 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 35 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 36 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 37 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 38 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 39 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 40 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 41 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 42 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 43 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 44 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 45 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f413raise*f400desc13) 46 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc14 46 b)
      (by decide +kernel) 0 b

theorem f400desc14_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f400desc14 *ᵥ x) := by
  exact natFour_descendant_step 13
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f413basis f414basis f400desc13 f400desc14 f413raise
    f400desc13_actual f413_actual_raise_block f400desc14_step x

#print axioms f400desc14_step
#print axioms f400desc14_actual
end TorusLean.BosonFiniteCertificate
