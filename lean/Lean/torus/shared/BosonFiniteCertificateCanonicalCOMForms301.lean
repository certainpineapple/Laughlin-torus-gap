import torus.shared.BosonFiniteCertificateCanonicalCompression301
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

theorem k301_actual_descendant_form1 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc1)ᴴ * k301actualM3 *
        complexify c301desc1) *ᵥ y) := by
  rw [c301desc1_actual x, c301desc1_actual y, canonicalOriginalM3Form_block,
    k301_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form1

theorem k301_actual_descendant_form2 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc2)ᴴ * k302actualM3 *
        complexify c301desc2) *ᵥ y) := by
  rw [c301desc2_actual x, c301desc2_actual y, canonicalOriginalM3Form_block,
    k302_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form2

theorem k301_actual_descendant_form3 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc3)ᴴ * k303actualM3 *
        complexify c301desc3) *ᵥ y) := by
  rw [c301desc3_actual x, c301desc3_actual y, canonicalOriginalM3Form_block,
    k303_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form3

theorem k301_actual_descendant_form4 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc4)ᴴ * k304actualM3 *
        complexify c301desc4) *ᵥ y) := by
  rw [c301desc4_actual x, c301desc4_actual y, canonicalOriginalM3Form_block,
    k304_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form4

theorem k301_actual_descendant_form5 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc5)ᴴ * k305actualM3 *
        complexify c301desc5) *ᵥ y) := by
  rw [c301desc5_actual x, c301desc5_actual y, canonicalOriginalM3Form_block,
    k305_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form5

theorem k301_actual_descendant_form6 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc6)ᴴ * k306actualM3 *
        complexify c301desc6) *ᵥ y) := by
  rw [c301desc6_actual x, c301desc6_actual y, canonicalOriginalM3Form_block,
    k306_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form6

theorem k301_actual_descendant_form7 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[6] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[6] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc7)ᴴ * k307actualM3 *
        complexify c301desc7) *ᵥ y) := by
  rw [c301desc7_actual x, c301desc7_actual y, canonicalOriginalM3Form_block,
    k307_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form7

theorem k301_actual_descendant_form8 (x y : Fin 0 → ℂ) :
    canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[7] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[7] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      star x ⬝ᵥ (((complexify c301desc8)ᴴ * k308actualM3 *
        complexify c301desc8) *ᵥ y) := by
  rw [c301desc8_actual x, c301desc8_actual y, canonicalOriginalM3Form_block,
    k308_all_original_row_channels, matrixCross_congruence]

#print axioms k301_actual_descendant_form8

/-- The displayed finite COM average acts by the genuine canonical raising
operator, then all 138 original row operators and the exact pair subtraction.
It is a finite list, not an infinite COM trace or torus thermal limit. -/
def k301actualFiniteCOMForm (x y : Fin 0 → ℂ) : ℂ :=
  (((2/3) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
  (((2/9) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
  (((1/27) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
  (((1/243) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
  (((1/2916) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
  (((1/43740) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
  (((1/787320) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[6] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[6] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) +
  (((1/16533720) : ℚ) : ℂ) * canonicalOriginalM3Form ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[7] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[7] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y)))

theorem k301_actual_finite_COM_form (x y : Fin 0 → ℂ) :
    k301actualFiniteCOMForm x y = star x ⬝ᵥ (k301finiteDescendantM3 *ᵥ y) := by
  unfold k301actualFiniteCOMForm k301finiteDescendantM3
  rw [k301_actual_descendant_form1, k301_actual_descendant_form2, k301_actual_descendant_form3, k301_actual_descendant_form4, k301_actual_descendant_form5, k301_actual_descendant_form6, k301_actual_descendant_form7, k301_actual_descendant_form8]
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

theorem k301_actual_finite_COM_source (x y : Fin 0 → ℂ) :
    k301actualFiniteCOMForm x y = star x ⬝ᵥ (complexify c301averageRaw *ᵥ y) := by
  rw [k301_actual_finite_COM_form, k301_finite_descendant_source]

#print axioms k301_actual_finite_COM_form
#print axioms k301_actual_finite_COM_source
end TorusLean.BosonFiniteCertificate
