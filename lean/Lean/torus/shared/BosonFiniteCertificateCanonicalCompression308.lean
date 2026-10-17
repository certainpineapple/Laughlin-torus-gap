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
def k308finiteDescendantM3 : Matrix (Fin 2) (Fin 2) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c308desc8)ᴴ * k308actualM3 * complexify c308desc8)

theorem k308_finite_descendant_source :
    k308finiteDescendantM3 = complexify c308averageRaw := by
  unfold k308finiteDescendantM3 c308averageRaw
  rw [k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k308rowCertifiedComparison : Matrix (Fin 2) (Fin 2) ℂ :=
  complexify c308sRaw - k308finiteDescendantM3 + (delta : ℂ) • complexify c308hRaw

theorem k308_row_certified_source :
    k308rowCertifiedComparison = complexify c308comparisonRaw := by
  rw [k308rowCertifiedComparison, k308_finite_descendant_source]
  simp only [c308comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k308_row_certified_positive : k308rowCertifiedComparison.PosSemidef := by
  rw [k308_row_certified_source]
  exact c308_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k308rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k308family
    (inverseGramCoefficient (complexify k308J) k308rowCertifiedComparison)

theorem k308_row_certified_operator_eq :
    k308rowCertifiedOperator = k308comparisonOperator := by
  unfold k308rowCertifiedOperator
  rw [k308_row_certified_source]
  rfl

theorem k308_row_certified_form (x y : Fin 2 → ℂ) :
    ip (familySynthesis k308family x).val
      (k308rowCertifiedOperator (familySynthesis k308family y)).val =
      star x ⬝ᵥ (k308rowCertifiedComparison *ᵥ y) := by
  rw [k308_row_certified_operator_eq, k308_row_certified_source]
  exact k308_comparison_operator_form x y

theorem k308_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k308rowCertifiedOperator f)).re := by
  rw [k308_row_certified_operator_eq]
  exact k308_comparison_lift_nonneg f

#print axioms k308_finite_descendant_source
#print axioms k308_row_certified_source
#print axioms k308_row_certified_positive
#print axioms k308_row_certified_form
#print axioms k308_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
