import torus.shared.BosonFiniteCertificateCanonicalActualHamiltonian306
import torus.shared.BosonFiniteCertificateCanonicalCOMForms306
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
def k306actualComparisonForm (x y : Fin 2 → ℂ) : ℂ :=
  ip (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y)))) -
    ip (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) -
    k306actualFiniteCOMForm x y +
    (delta : ℂ) * ip (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y)))

theorem k306_actual_comparison_form (x y : Fin 2 → ℂ) :
    k306actualComparisonForm x y = star x ⬝ᵥ (k306rowCertifiedComparison *ᵥ y) := by
  unfold k306actualComparisonForm
  simp only [k306_actual_common_pair_hamiltonian_square_form,
    k306_actual_common_pair_hamiltonian_form, k306_actual_finite_COM_form, matrixCross_congruence]
  simp only [k306rowCertifiedComparison, c306sRaw, c306hRaw, planarSingleForm,
    complexify_mul_rect, complexify_transpose_rect, complexify_sub_rect,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.add_mulVec,
    dotProduct_sub, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem k306_actual_comparison_nonneg (x : Fin 2 → ℂ) :
    0 ≤ (k306actualComparisonForm x x).re := by
  rw [k306_actual_comparison_form]
  exact (Complex.nonneg_iff.mp (k306_row_certified_positive.dotProduct_mulVec_nonneg x)).1

/-- The certified N=3 Riesz operator has precisely the actual auxiliary
comparison cross form on the stated relative family. It is still a zero
extension off that family, not an unrestricted original-operator identity. -/
theorem k306_actual_comparison_operator_form (x y : Fin 2 → ℂ) :
    ip (familySynthesis k306family x).val
      (k306rowCertifiedOperator (familySynthesis k306family y)).val =
      k306actualComparisonForm x y := by
  rw [k306_row_certified_form, k306_actual_comparison_form]

#print axioms k306_actual_comparison_form
#print axioms k306_actual_comparison_nonneg
#print axioms k306_actual_comparison_operator_form
end TorusLean.BosonFiniteCertificate
