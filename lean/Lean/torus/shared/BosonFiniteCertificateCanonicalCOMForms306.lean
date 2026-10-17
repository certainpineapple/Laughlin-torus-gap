import torus.shared.BosonFiniteCertificateCanonicalCompression306
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

theorem k306_actual_descendant_form6 (x y : Fin 2 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c306desc6)ᴴ * k306actualM3 *
        complexify c306desc6) *ᵥ y) := by
  rw [c306desc6_actual x, c306desc6_actual y, canonicalOriginalM3Form_block,
    k306_all_original_row_channels, matrixCross_congruence]

#print axioms k306_actual_descendant_form6

theorem k306_actual_descendant_form7 (x y : Fin 2 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c306desc7)ᴴ * k307actualM3 *
        complexify c306desc7) *ᵥ y) := by
  rw [c306desc7_actual x, c306desc7_actual y, canonicalOriginalM3Form_block,
    k307_all_original_row_channels, matrixCross_congruence]

#print axioms k306_actual_descendant_form7

theorem k306_actual_descendant_form8 (x y : Fin 2 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c306desc8)ᴴ * k308actualM3 *
        complexify c306desc8) *ᵥ y) := by
  rw [c306desc8_actual x, c306desc8_actual y, canonicalOriginalM3Form_block,
    k308_all_original_row_channels, matrixCross_congruence]

#print axioms k306_actual_descendant_form8

/-- The displayed finite COM average acts by the genuine canonical raising
operator, then all 138 original row operators and the exact pair subtraction.
It is a finite list, not an infinite COM trace or torus thermal limit. -/
def k306actualFiniteCOMForm (x y : Fin 2 → ℂ) : ℂ :=
  (((2/3) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) +
  (((2/9) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) +
  (((1/27) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y)))

theorem k306_actual_finite_COM_form (x y : Fin 2 → ℂ) :
    k306actualFiniteCOMForm x y = star x ⬝ᵥ (k306finiteDescendantM3 *ᵥ y) := by
  unfold k306actualFiniteCOMForm k306finiteDescendantM3
  rw [k306_actual_descendant_form6, k306_actual_descendant_form7, k306_actual_descendant_form8]
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

theorem k306_actual_finite_COM_source (x y : Fin 2 → ℂ) :
    k306actualFiniteCOMForm x y = star x ⬝ᵥ (complexify c306averageRaw *ᵥ y) := by
  rw [k306_actual_finite_COM_form, k306_finite_descendant_source]

#print axioms k306_actual_finite_COM_form
#print axioms k306_actual_finite_COM_source
end TorusLean.BosonFiniteCertificate
