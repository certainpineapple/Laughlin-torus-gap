import torus.shared.BosonFiniteCertificateCanonicalActualHamiltonian302
import torus.shared.BosonFiniteCertificateCanonicalCOMForms302
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

/-- Actual finite planar comparison form: the genuine pair differential H
composed with itself, minus H, minus the displayed original-row finite COM
average, plus delta H. No torus single3 or infinite COM identity is asserted. -/
def k302actualComparisonForm (x y : Fin 1 → ℂ) : ℂ :=
  ip (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ y))) -
    k302actualFiniteCOMForm x y +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ y)))

theorem k302_actual_comparison_form (x y : Fin 1 → ℂ) :
    k302actualComparisonForm x y = star x ⬝ᵥ (k302rowCertifiedComparison *ᵥ y) := by
  unfold k302actualComparisonForm
  simp only [k302_actual_common_pair_hamiltonian_square_form,
    k302_actual_common_pair_hamiltonian_form, k302_actual_finite_COM_form, matrixCross_congruence]
  simp only [k302rowCertifiedComparison, c302sRaw, c302hRaw, planarSingleForm,
    complexify_mul_rect, complexify_transpose_rect, complexify_sub_rect,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.add_mulVec,
    dotProduct_sub, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem k302_actual_comparison_nonneg (x : Fin 1 → ℂ) :
    0 ≤ (k302actualComparisonForm x x).re := by
  rw [k302_actual_comparison_form]
  exact (Complex.nonneg_iff.mp (k302_row_certified_positive.dotProduct_mulVec_nonneg x)).1

/-- The certified N=3 Riesz operator has precisely the actual auxiliary
comparison cross form on the stated relative family. It is still a zero
extension off that family, not an unrestricted original-operator identity. -/
theorem k302_actual_comparison_operator_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k302family x).val
      (k302rowCertifiedOperator (familySynthesis k302family y)).val =
      k302actualComparisonForm x y := by
  rw [k302_row_certified_form, k302_actual_comparison_form]

#print axioms k302_actual_comparison_form
#print axioms k302_actual_comparison_nonneg
#print axioms k302_actual_comparison_operator_form
end TorusLean.BosonFiniteCertificate
