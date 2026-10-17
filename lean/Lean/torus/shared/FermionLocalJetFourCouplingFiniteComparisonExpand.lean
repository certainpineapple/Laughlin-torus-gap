import torus.shared.FermionLocalJetFourCouplingFiniteComparisonMiddle

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

theorem original_four_comparison_matrix_expansion (D : ℕ) :
    fourComparisonFinMatrix D = fourCertificateDiagonal D -
      originalCopyRootDiagonal D * (integerFourErrorMatrix D).map (Rat.castHom ℂ) *
        originalCopyRootDiagonal D := by
  exact congrArg (fun A : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℂ =>
    fourCertificateDiagonal D - A) (certificateFourMatrixFin_eq_integer_error D)

#print axioms original_four_comparison_matrix_expansion
end TorusLean.Shared.FermionLocalJet.FourCoupling
