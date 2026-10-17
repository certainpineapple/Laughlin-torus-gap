import torus.shared.BosonFiniteCertificateCanonicalActualHamiltonian301
import torus.shared.BosonFiniteCertificateCanonicalCOMForms301
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
def k301actualComparisonForm (x y : Fin 0 → ℂ) : ℂ :=
  ip (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) -
    k301actualFiniteCOMForm x y +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y)))

theorem k301_actual_comparison_form (x y : Fin 0 → ℂ) :
    k301actualComparisonForm x y = star x ⬝ᵥ (k301rowCertifiedComparison *ᵥ y) := by
  unfold k301actualComparisonForm
  simp only [k301_actual_common_pair_hamiltonian_square_form,
    k301_actual_common_pair_hamiltonian_form, k301_actual_finite_COM_form, matrixCross_congruence]
  simp only [k301rowCertifiedComparison, c301sRaw, c301hRaw, planarSingleForm,
    complexify_mul_rect, complexify_transpose_rect, complexify_sub_rect,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.add_mulVec,
    dotProduct_sub, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem k301_actual_comparison_nonneg (x : Fin 0 → ℂ) :
    0 ≤ (k301actualComparisonForm x x).re := by
  rw [k301_actual_comparison_form]
  exact (Complex.nonneg_iff.mp (k301_row_certified_positive.dotProduct_mulVec_nonneg x)).1

/-- The certified N=3 Riesz operator has precisely the actual auxiliary
comparison cross form on the stated relative family. It is still a zero
extension off that family, not an unrestricted original-operator identity. -/
theorem k301_actual_comparison_operator_form (x y : Fin 0 → ℂ) :
    ip (familySynthesis k301family x).val
      (k301rowCertifiedOperator (familySynthesis k301family y)).val =
      k301actualComparisonForm x y := by
  rw [k301_row_certified_form, k301_actual_comparison_form]

#print axioms k301_actual_comparison_form
#print axioms k301_actual_comparison_nonneg
#print axioms k301_actual_comparison_operator_form
end TorusLean.BosonFiniteCertificate
