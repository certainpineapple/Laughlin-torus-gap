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
def k304finiteDescendantM3 : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c304desc4)ᴴ * k304actualM3 * complexify c304desc4) +
  (((2/9) : ℚ) : ℂ) • ((complexify c304desc5)ᴴ * k305actualM3 * complexify c304desc5) +
  (((1/27) : ℚ) : ℂ) • ((complexify c304desc6)ᴴ * k306actualM3 * complexify c304desc6) +
  (((1/243) : ℚ) : ℂ) • ((complexify c304desc7)ᴴ * k307actualM3 * complexify c304desc7) +
  (((1/2916) : ℚ) : ℂ) • ((complexify c304desc8)ᴴ * k308actualM3 * complexify c304desc8)

theorem k304_finite_descendant_source :
    k304finiteDescendantM3 = complexify c304averageRaw := by
  unfold k304finiteDescendantM3 c304averageRaw
  rw [k304_actual_M3_raw, k305_actual_M3_raw, k306_actual_M3_raw, k307_actual_M3_raw, k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k304rowCertifiedComparison : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c304sRaw - k304finiteDescendantM3 + (delta : ℂ) • complexify c304hRaw

theorem k304_row_certified_source :
    k304rowCertifiedComparison = complexify c304comparisonRaw := by
  rw [k304rowCertifiedComparison, k304_finite_descendant_source]
  simp only [c304comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k304_row_certified_positive : k304rowCertifiedComparison.PosSemidef := by
  rw [k304_row_certified_source]
  exact c304_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k304rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k304family
    (inverseGramCoefficient (complexify k304J) k304rowCertifiedComparison)

theorem k304_row_certified_operator_eq :
    k304rowCertifiedOperator = k304comparisonOperator := by
  unfold k304rowCertifiedOperator
  rw [k304_row_certified_source]
  rfl

theorem k304_row_certified_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k304family x).val
      (k304rowCertifiedOperator (familySynthesis k304family y)).val =
      star x ⬝ᵥ (k304rowCertifiedComparison *ᵥ y) := by
  rw [k304_row_certified_operator_eq, k304_row_certified_source]
  exact k304_comparison_operator_form x y

theorem k304_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k304rowCertifiedOperator f)).re := by
  rw [k304_row_certified_operator_eq]
  exact k304_comparison_lift_nonneg f

#print axioms k304_finite_descendant_source
#print axioms k304_row_certified_source
#print axioms k304_row_certified_positive
#print axioms k304_row_certified_form
#print axioms k304_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
