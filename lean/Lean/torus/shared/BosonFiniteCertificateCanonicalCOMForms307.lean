import torus.shared.BosonFiniteCertificateCanonicalCompression307
import torus.shared.BosonFiniteCertificateCanonicalCOMRaise
import torus.shared.BosonFiniteCertificateCanonicalFormsCore
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexOrder
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization

theorem k307_actual_descendant_form7 (x y : Fin 1 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c307desc7)ᴴ * k307actualM3 *
        complexify c307desc7) *ᵥ y) := by
  rw [c307desc7_actual x, c307desc7_actual y, canonicalOriginalM3Form_block,
    k307_all_original_row_channels, matrixCross_congruence]

#print axioms k307_actual_descendant_form7

theorem k307_actual_descendant_form8 (x y : Fin 1 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c307desc8)ᴴ * k308actualM3 *
        complexify c307desc8) *ᵥ y) := by
  rw [c307desc8_actual x, c307desc8_actual y, canonicalOriginalM3Form_block,
    k308_all_original_row_channels, matrixCross_congruence]

#print axioms k307_actual_descendant_form8

/-- The displayed finite COM average acts by the genuine canonical raising
operator, then all 138 original row operators and the exact pair subtraction.
It is a finite list, not an infinite COM trace or torus thermal limit. -/
def k307actualFiniteCOMForm (x y : Fin 1 → ℂ) : ℂ :=
  (((2/3) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))) +
  (((2/9) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y)))

theorem k307_actual_finite_COM_form (x y : Fin 1 → ℂ) :
    k307actualFiniteCOMForm x y = star x ⬝ᵥ (k307finiteDescendantM3 *ᵥ y) := by
  unfold k307actualFiniteCOMForm k307finiteDescendantM3
  rw [k307_actual_descendant_form7, k307_actual_descendant_form8]
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

theorem k307_actual_finite_COM_source (x y : Fin 1 → ℂ) :
    k307actualFiniteCOMForm x y = star x ⬝ᵥ (complexify c307averageRaw *ᵥ y) := by
  rw [k307_actual_finite_COM_form, k307_finite_descendant_source]

#print axioms k307_actual_finite_COM_form
#print axioms k307_actual_finite_COM_source
end TorusLean.BosonFiniteCertificate
