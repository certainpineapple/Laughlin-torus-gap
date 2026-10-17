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
def k303finiteDescendantM3 : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c303desc3)ᴴ * k303actualM3 * complexify c303desc3) +
  (((2/9) : ℚ) : ℂ) • ((complexify c303desc4)ᴴ * k304actualM3 * complexify c303desc4) +
  (((1/27) : ℚ) : ℂ) • ((complexify c303desc5)ᴴ * k305actualM3 * complexify c303desc5) +
  (((1/243) : ℚ) : ℂ) • ((complexify c303desc6)ᴴ * k306actualM3 * complexify c303desc6) +
  (((1/2916) : ℚ) : ℂ) • ((complexify c303desc7)ᴴ * k307actualM3 * complexify c303desc7) +
  (((1/43740) : ℚ) : ℂ) • ((complexify c303desc8)ᴴ * k308actualM3 * complexify c303desc8)

theorem k303_finite_descendant_source :
    k303finiteDescendantM3 = complexify c303averageRaw := by
  unfold k303finiteDescendantM3 c303averageRaw
  rw [k303_actual_M3_raw, k304_actual_M3_raw, k305_actual_M3_raw, k306_actual_M3_raw, k307_actual_M3_raw, k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k303rowCertifiedComparison : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c303sRaw - k303finiteDescendantM3 + (delta : ℂ) • complexify c303hRaw

theorem k303_row_certified_source :
    k303rowCertifiedComparison = complexify c303comparisonRaw := by
  rw [k303rowCertifiedComparison, k303_finite_descendant_source]
  simp only [c303comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k303_row_certified_positive : k303rowCertifiedComparison.PosSemidef := by
  rw [k303_row_certified_source]
  exact c303_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k303rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k303family
    (inverseGramCoefficient (complexify k303J) k303rowCertifiedComparison)

theorem k303_row_certified_operator_eq :
    k303rowCertifiedOperator = k303comparisonOperator := by
  unfold k303rowCertifiedOperator
  rw [k303_row_certified_source]
  rfl

theorem k303_row_certified_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k303family x).val
      (k303rowCertifiedOperator (familySynthesis k303family y)).val =
      star x ⬝ᵥ (k303rowCertifiedComparison *ᵥ y) := by
  rw [k303_row_certified_operator_eq, k303_row_certified_source]
  exact k303_comparison_operator_form x y

theorem k303_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k303rowCertifiedOperator f)).re := by
  rw [k303_row_certified_operator_eq]
  exact k303_comparison_lift_nonneg f

#print axioms k303_finite_descendant_source
#print axioms k303_row_certified_source
#print axioms k303_row_certified_positive
#print axioms k303_row_certified_form
#print axioms k303_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
