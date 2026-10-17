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
def k305finiteDescendantM3 : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c305desc5)ᴴ * k305actualM3 * complexify c305desc5) +
  (((2/9) : ℚ) : ℂ) • ((complexify c305desc6)ᴴ * k306actualM3 * complexify c305desc6) +
  (((1/27) : ℚ) : ℂ) • ((complexify c305desc7)ᴴ * k307actualM3 * complexify c305desc7) +
  (((1/243) : ℚ) : ℂ) • ((complexify c305desc8)ᴴ * k308actualM3 * complexify c305desc8)

theorem k305_finite_descendant_source :
    k305finiteDescendantM3 = complexify c305averageRaw := by
  unfold k305finiteDescendantM3 c305averageRaw
  rw [k305_actual_M3_raw, k306_actual_M3_raw, k307_actual_M3_raw, k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k305rowCertifiedComparison : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c305sRaw - k305finiteDescendantM3 + (delta : ℂ) • complexify c305hRaw

theorem k305_row_certified_source :
    k305rowCertifiedComparison = complexify c305comparisonRaw := by
  rw [k305rowCertifiedComparison, k305_finite_descendant_source]
  simp only [c305comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k305_row_certified_positive : k305rowCertifiedComparison.PosSemidef := by
  rw [k305_row_certified_source]
  exact c305_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k305rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k305family
    (inverseGramCoefficient (complexify k305J) k305rowCertifiedComparison)

theorem k305_row_certified_operator_eq :
    k305rowCertifiedOperator = k305comparisonOperator := by
  unfold k305rowCertifiedOperator
  rw [k305_row_certified_source]
  rfl

theorem k305_row_certified_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k305family x).val
      (k305rowCertifiedOperator (familySynthesis k305family y)).val =
      star x ⬝ᵥ (k305rowCertifiedComparison *ᵥ y) := by
  rw [k305_row_certified_operator_eq, k305_row_certified_source]
  exact k305_comparison_operator_form x y

theorem k305_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k305rowCertifiedOperator f)).re := by
  rw [k305_row_certified_operator_eq]
  exact k305_comparison_lift_nonneg f

#print axioms k305_finite_descendant_source
#print axioms k305_row_certified_source
#print axioms k305_row_certified_positive
#print axioms k305_row_certified_form
#print axioms k305_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
