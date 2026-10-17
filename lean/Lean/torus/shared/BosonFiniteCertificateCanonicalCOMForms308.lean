import torus.shared.BosonFiniteCertificateCanonicalCompression308
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

theorem k308_actual_descendant_form8 (x y : Fin 2 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c308desc8)ᴴ * k308actualM3 *
        complexify c308desc8) *ᵥ y) := by
  rw [c308desc8_actual x, c308desc8_actual y, canonicalOriginalM3Form_block,
    k308_all_original_row_channels, matrixCross_congruence]

#print axioms k308_actual_descendant_form8

/-- The displayed finite COM average acts by the genuine canonical raising
operator, then all 138 original row operators and the exact pair subtraction.
It is a finite list, not an infinite COM trace or torus thermal limit. -/
def k308actualFiniteCOMForm (x y : Fin 2 → ℂ) : ℂ :=
  (((2/3) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y)))

theorem k308_actual_finite_COM_form (x y : Fin 2 → ℂ) :
    k308actualFiniteCOMForm x y = star x ⬝ᵥ (k308finiteDescendantM3 *ᵥ y) := by
  unfold k308actualFiniteCOMForm k308finiteDescendantM3
  rw [k308_actual_descendant_form8]
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

theorem k308_actual_finite_COM_source (x y : Fin 2 → ℂ) :
    k308actualFiniteCOMForm x y = star x ⬝ᵥ (complexify c308averageRaw *ᵥ y) := by
  rw [k308_actual_finite_COM_form, k308_finite_descendant_source]

#print axioms k308_actual_finite_COM_form
#print axioms k308_actual_finite_COM_source
end TorusLean.BosonFiniteCertificate
