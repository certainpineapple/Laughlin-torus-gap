import torus.shared.BosonFiniteCertificateCanonicalRowCore
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

/-- Every row parameter, hence every original frozen row, is now an actual
canonical finite-label differential operator on the source occupation basis. -/
theorem k300_actual_canonical_row (t : Fin 4) (row : List ℤ) (a : Fin 1) :
    canonicalFrozenRow9 t.val row
      (canonicalMonomial (factorialScale 8) (k300occ a)) =
      ((threeRowAction t.val row (p300basis a) : ℂ) / 1000000000000) •
        canonicalMonomial (factorialScale 8) (Finsupp.single (fin9 (0-t.val)) 1) := by
  have h := conjugated_finitePaperRow9_action factorialRoot9 factorialRoot9_ne_zero
    t.val 0 row (p300basis a) (k300_source_labels_bounded a) (by omega)
    (frozen_rows_labels_bounded t) (p300_all_word_outputs t a)
  rw [k300_canonical_source_word, scaledWord_single_factorial] at h
  exact h

/-- Exact complex cross-form of the genuine row square, with no assumed
operator-action or PSD premise. -/
theorem k300_actual_canonical_row_form (t : Fin 4) (row : List ℤ)
    (x y : Fin 1 → ℂ) :
    ip (canonicalFrozenRow9 t.val row (canonicalBlock (factorialScale 8) k300occ x))
      (canonicalFrozenRow9 t.val row (canonicalBlock (factorialScale 8) k300occ y)) =
      star x ⬝ᵥ (complexify (rationalRowSquare (0-t.val).factorial
        (fun a => threeRowAction t.val row (p300basis a))) *ᵥ y) := by
  rw [rationalRowSquare_complex]
  have h := canonicalBlock_row_form (factorialScale 8) k300occ
    (Finsupp.single (fin9 (0-t.val)) 1) (canonicalFrozenRow9 t.val row)
    (fun a => (threeRowAction t.val row (p300basis a) : ℂ) / 1000000000000)
    (fun a => k300_actual_canonical_row t row a) x y
  rw [factorial_output_metric (0-t.val) (by omega)] at h
  exact h

#print axioms k300_actual_canonical_row
#print axioms k300_actual_canonical_row_form
end TorusLean.BosonFiniteCertificate
