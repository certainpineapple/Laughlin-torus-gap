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
def k300finiteDescendantM3 : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3) : ℚ) : ℂ) • ((complexify c300desc0)ᴴ * k300actualM3 * complexify c300desc0) +
  (((2/9) : ℚ) : ℂ) • ((complexify c300desc1)ᴴ * k301actualM3 * complexify c300desc1) +
  (((1/27) : ℚ) : ℂ) • ((complexify c300desc2)ᴴ * k302actualM3 * complexify c300desc2) +
  (((1/243) : ℚ) : ℂ) • ((complexify c300desc3)ᴴ * k303actualM3 * complexify c300desc3) +
  (((1/2916) : ℚ) : ℂ) • ((complexify c300desc4)ᴴ * k304actualM3 * complexify c300desc4) +
  (((1/43740) : ℚ) : ℂ) • ((complexify c300desc5)ᴴ * k305actualM3 * complexify c300desc5) +
  (((1/787320) : ℚ) : ℂ) • ((complexify c300desc6)ᴴ * k306actualM3 * complexify c300desc6) +
  (((1/16533720) : ℚ) : ℂ) • ((complexify c300desc7)ᴴ * k307actualM3 * complexify c300desc7) +
  (((1/396809280) : ℚ) : ℂ) • ((complexify c300desc8)ᴴ * k308actualM3 * complexify c300desc8)

theorem k300_finite_descendant_source :
    k300finiteDescendantM3 = complexify c300averageRaw := by
  unfold k300finiteDescendantM3 c300averageRaw
  rw [k300_actual_M3_raw, k301_actual_M3_raw, k302_actual_M3_raw, k303_actual_M3_raw, k304_actual_M3_raw, k305_actual_M3_raw, k306_actual_M3_raw, k307_actual_M3_raw, k308_actual_M3_raw]
  simp only [complexify_add_rect, complexify_smul_rat, complexify_mul_rect,
    complexify_transpose_rect]

/-- The original finite comparison, with its negative M3 term built from
true canonical row-square forms and the displayed finite descendant matrices. -/
def k300rowCertifiedComparison : Matrix (Fin 1) (Fin 1) ℂ :=
  complexify c300sRaw - k300finiteDescendantM3 + (delta : ℂ) • complexify c300hRaw

theorem k300_row_certified_source :
    k300rowCertifiedComparison = complexify c300comparisonRaw := by
  rw [k300rowCertifiedComparison, k300_finite_descendant_source]
  simp only [c300comparisonRaw, complexify_add_rect, complexify_sub_rect,
    complexify_smul_rat]

theorem k300_row_certified_positive : k300rowCertifiedComparison.PosSemidef := by
  rw [k300_row_certified_source]
  exact c300_source_comparison_positive

/-- Zero extension of this concrete finite relative comparison form in the
same canonical N=3 carrier. No equality off the relative span to an original
uncompressed operator is asserted. -/
def k300rowCertifiedOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k300family
    (inverseGramCoefficient (complexify k300J) k300rowCertifiedComparison)

theorem k300_row_certified_operator_eq :
    k300rowCertifiedOperator = k300comparisonOperator := by
  unfold k300rowCertifiedOperator
  rw [k300_row_certified_source]
  rfl

theorem k300_row_certified_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k300family x).val
      (k300rowCertifiedOperator (familySynthesis k300family y)).val =
      star x ⬝ᵥ (k300rowCertifiedComparison *ᵥ y) := by
  rw [k300_row_certified_operator_eq, k300_row_certified_source]
  exact k300_comparison_operator_form x y

theorem k300_row_certified_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k300rowCertifiedOperator f)).re := by
  rw [k300_row_certified_operator_eq]
  exact k300_comparison_lift_nonneg f

#print axioms k300_finite_descendant_source
#print axioms k300_row_certified_source
#print axioms k300_row_certified_positive
#print axioms k300_row_certified_form
#print axioms k300_row_certified_lift_nonneg
end TorusLean.BosonFiniteCertificate
