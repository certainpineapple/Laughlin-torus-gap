import torus.shared.BosonFiniteCertificateCanonicalCompressionCore
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexOrder
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateRealization

/-- The stated finite list of canonical descendant form compressions. This
is not an infinite COM trace or a torus thermal-transfer theorem. -/
def k301finiteDescendantM3 : Matrix (Fin 0) (Fin 0) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c301desc1)ᴴ * k301actualM3 * complexify c301desc1) +
  (((2/9) : ℚ) : ℂ) • ((complexify c301desc2)ᴴ * k302actualM3 * complexify c301desc2) +
  (((1/27) : ℚ) : ℂ) • ((complexify c301desc3)ᴴ * k303actualM3 * complexify c301desc3) +
  (((1/243) : ℚ) : ℂ) • ((complexify c301desc4)ᴴ * k304actualM3 * complexify c301desc4) +
  (((1/2916) : ℚ) : ℂ) • ((complexify c301desc5)ᴴ * k305actualM3 * complexify c301desc5) +
  (((1/43740) : ℚ) : ℂ) • ((complexify c301desc6)ᴴ * k306actualM3 * complexify c301desc6) +
  (((1/787320) : ℚ) : ℂ) • ((complexify c301desc7)ᴴ * k307actualM3 * complexify c301desc7) +
  (((1/16533720) : ℚ) : ℂ) • ((complexify c301desc8)ᴴ * k308actualM3 * complexify c301desc8)

theorem k301_finite_descendant_source :
    k301finiteDescendantM3 = complexify c301averageRaw := by
  unfold k301finiteDescendantM3 c301averageRaw
  rw [k301_actual_M3_raw, k302_actual_M3_raw, k303_actual_M3_raw, k304_actual_M3_raw, k305_actual_M3_raw, k306_actual_M3_raw, k307_actual_M3_raw, k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k301rowCertifiedComparison : Matrix (Fin 0) (Fin 0) ℂ :=
  complexify c301sRaw - k301finiteDescendantM3 + (delta : ℂ) • complexify c301hRaw

theorem k301_row_certified_source :
    k301rowCertifiedComparison = complexify c301comparisonRaw := by
  rw [k301rowCertifiedComparison, k301_finite_descendant_source]
  simp only [c301comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k301_row_certified_positive : k301rowCertifiedComparison.PosSemidef := by
  rw [k301_row_certified_source]
  exact c301_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k301rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k301family
    (inverseGramCoefficient (complexify k301J) k301rowCertifiedComparison)

theorem k301_row_certified_operator_eq :
    k301rowCertifiedOperator = k301comparisonOperator := by
  unfold k301rowCertifiedOperator
  rw [k301_row_certified_source]
  rfl

theorem k301_row_certified_form (x y : Fin 0 → ℂ) :
    ip (familySynthesis k301family x).val
      (k301rowCertifiedOperator (familySynthesis k301family y)).val =
      star x ⬝ᵥ (k301rowCertifiedComparison *ᵥ y) := by
  rw [k301_row_certified_operator_eq, k301_row_certified_source]
  exact k301_comparison_operator_form x y

theorem k301_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k301rowCertifiedOperator f)).re := by
  rw [k301_row_certified_operator_eq]
  exact k301_comparison_lift_nonneg f

#print axioms k301_finite_descendant_source
#print axioms k301_row_certified_source
#print axioms k301_row_certified_positive
#print axioms k301_row_certified_form
#print axioms k301_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
