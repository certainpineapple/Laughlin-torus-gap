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
theorem k307_actual_canonical_row (t : Fin 4) (row : List ℤ) (a : Fin 8) :
    canonicalFrozenRow9 t.val row
      (canonicalMonomial (factorialScale 8) (k307occ a)) =
      ((threeRowAction t.val row (p307basis a) : ℂ) / 1000000000000) •
        canonicalMonomial (factorialScale 8) (Finsupp.single (fin9 (7-t.val)) 1) := by
  have h := conjugated_finitePaperRow9_action factorialRoot9 factorialRoot9_ne_zero
    t.val 7 row (p307basis a) (k307_source_labels_bounded a) (by omega)
    (frozen_rows_labels_bounded t) (p307_all_word_outputs t a)
  rw [k307_canonical_source_word, scaledWord_single_factorial] at h
  exact h

/-- Exact complex cross-form of the genuine row square, with no assumed
operator-action or PSD premise. -/
theorem k307_actual_canonical_row_form (t : Fin 4) (row : List ℤ)
    (x y : Fin 8 → ℂ) :
    ip (canonicalFrozenRow9 t.val row (canonicalBlock (factorialScale 8) k307occ x))
      (canonicalFrozenRow9 t.val row (canonicalBlock (factorialScale 8) k307occ y)) =
      star x ⬝ᵥ (complexify (rationalRowSquare (7-t.val).factorial
        (fun a => threeRowAction t.val row (p307basis a))) *ᵥ y) := by
  rw [rationalRowSquare_complex]
  have h := canonicalBlock_row_form (factorialScale 8) k307occ
    (Finsupp.single (fin9 (7-t.val)) 1) (canonicalFrozenRow9 t.val row)
    (fun a => (threeRowAction t.val row (p307basis a) : ℂ) / 1000000000000)
    (fun a => k307_actual_canonical_row t row a) x y
  rw [factorial_output_metric (7-t.val) (by omega)] at h
  exact h

#print axioms k307_actual_canonical_row
#print axioms k307_actual_canonical_row_form
end TorusLean.BosonFiniteCertificate
