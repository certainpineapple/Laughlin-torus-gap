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
def k307finiteDescendantM3 : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c307desc7)ᴴ * k307actualM3 * complexify c307desc7) +
  (((2/9) : ℚ) : ℂ) • ((complexify c307desc8)ᴴ * k308actualM3 * complexify c307desc8)

theorem k307_finite_descendant_source :
    k307finiteDescendantM3 = complexify c307averageRaw := by
  unfold k307finiteDescendantM3 c307averageRaw
  rw [k307_actual_M3_raw, k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k307rowCertifiedComparison : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c307sRaw - k307finiteDescendantM3 + (delta : ℂ) • complexify c307hRaw

theorem k307_row_certified_source :
    k307rowCertifiedComparison = complexify c307comparisonRaw := by
  rw [k307rowCertifiedComparison, k307_finite_descendant_source]
  simp only [c307comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k307_row_certified_positive : k307rowCertifiedComparison.PosSemidef := by
  rw [k307_row_certified_source]
  exact c307_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k307rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k307family
    (inverseGramCoefficient (complexify k307J) k307rowCertifiedComparison)

theorem k307_row_certified_operator_eq :
    k307rowCertifiedOperator = k307comparisonOperator := by
  unfold k307rowCertifiedOperator
  rw [k307_row_certified_source]
  rfl

theorem k307_row_certified_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k307family x).val
      (k307rowCertifiedOperator (familySynthesis k307family y)).val =
      star x ⬝ᵥ (k307rowCertifiedComparison *ᵥ y) := by
  rw [k307_row_certified_operator_eq, k307_row_certified_source]
  exact k307_comparison_operator_form x y

theorem k307_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k307rowCertifiedOperator f)).re := by
  rw [k307_row_certified_operator_eq]
  exact k307_comparison_lift_nonneg f

#print axioms k307_finite_descendant_source
#print axioms k307_row_certified_source
#print axioms k307_row_certified_positive
#print axioms k307_row_certified_form
#print axioms k307_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
