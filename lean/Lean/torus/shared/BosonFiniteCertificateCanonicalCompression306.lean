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
def k306finiteDescendantM3 : Matrix (Fin 2) (Fin 2) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c306desc6)ᴴ * k306actualM3 * complexify c306desc6) +
  (((2/9) : ℚ) : ℂ) • ((complexify c306desc7)ᴴ * k307actualM3 * complexify c306desc7) +
  (((1/27) : ℚ) : ℂ) • ((complexify c306desc8)ᴴ * k308actualM3 * complexify c306desc8)

theorem k306_finite_descendant_source :
    k306finiteDescendantM3 = complexify c306averageRaw := by
  unfold k306finiteDescendantM3 c306averageRaw
  rw [k306_actual_M3_raw, k307_actual_M3_raw, k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k306rowCertifiedComparison : Matrix (Fin 2) (Fin 2) ℂ :=
  complexify c306sRaw - k306finiteDescendantM3 + (delta : ℂ) • complexify c306hRaw

theorem k306_row_certified_source :
    k306rowCertifiedComparison = complexify c306comparisonRaw := by
  rw [k306rowCertifiedComparison, k306_finite_descendant_source]
  simp only [c306comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k306_row_certified_positive : k306rowCertifiedComparison.PosSemidef := by
  rw [k306_row_certified_source]
  exact c306_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k306rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k306family
    (inverseGramCoefficient (complexify k306J) k306rowCertifiedComparison)

theorem k306_row_certified_operator_eq :
    k306rowCertifiedOperator = k306comparisonOperator := by
  unfold k306rowCertifiedOperator
  rw [k306_row_certified_source]
  rfl

theorem k306_row_certified_form (x y : Fin 2 → ℂ) :
    ip (familySynthesis k306family x).val
      (k306rowCertifiedOperator (familySynthesis k306family y)).val =
      star x ⬝ᵥ (k306rowCertifiedComparison *ᵥ y) := by
  rw [k306_row_certified_operator_eq, k306_row_certified_source]
  exact k306_comparison_operator_form x y

theorem k306_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k306rowCertifiedOperator f)).re := by
  rw [k306_row_certified_operator_eq]
  exact k306_comparison_lift_nonneg f

#print axioms k306_finite_descendant_source
#print axioms k306_row_certified_source
#print axioms k306_row_certified_positive
#print axioms k306_row_certified_form
#print axioms k306_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
