import torus.shared.BosonFiniteCertificateCanonicalTransport
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate

/-- This is the actual finite normal-order row under an invertible variable
change, acting on the whole finite-label polynomial core. It is not a Riesz
operator defined from the desired form matrix. -/
def canonicalFrozenRow9 (t : ℕ) (row : List ℤ) :
    Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  conjugateOperator factorialRoot9 factorialRoot9_ne_zero (finitePaperRow9 t row)

theorem scaledWord_single_factorial (j : Fin 9) :
    scaledWord factorialRoot9 [j] =
      canonicalMonomial (factorialScale 8) (Finsupp.single j 1) := by
  change scaledWord (fun q => (Real.sqrt (factorialScale 8 q : ℝ) : ℂ)) [j] = _
  simpa only [wordOccupation, add_zero] using
    scaledWord_eq_canonicalMonomial (factorialScale 8) [j]

theorem factorial_output_metric (q : ℕ) (hq : q < 9) :
    occupationMetricWeight (factorialScale 8) (Finsupp.single (fin9 q) 1) = q.factorial := by
  rw [occupationMetricWeight_single]
  simp only [factorialScale, fin9, Nat.mod_eq_of_lt hq]

/-- Rational row-square entries with their true one-particle factorial metric. -/
def rationalRowSquare {n : ℕ} (g : ℕ) (c : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b => (g : ℚ) * ((c a : ℚ) / 1000000000000) * ((c b : ℚ) / 1000000000000)

theorem rationalRowSquare_complex {n : ℕ} (g : ℕ) (c : Fin n → ℤ) :
    complexify (rationalRowSquare g c) =
      (fun a b => (g : ℂ) * star ((c a : ℂ) / 1000000000000) *
        ((c b : ℂ) / 1000000000000)) := by
  ext a b
  simp [complexify, rationalRowSquare]

end TorusLean.BosonFiniteCertificate
