import torus.shared.FermionLocalJetFourCouplingFiniteComparisonExpand
import torus.shared.FermionLocalJetFourCouplingFiniteComparisonAlgebra
import torus.shared.FermionLocalJetFourCouplingFiniteComparisonCast

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

theorem original_four_compression_identity (D : ℕ) :
    (((originalSlaterMatrixFin D)ᴴ*originalSlaterMatrixFin D) *
      fourComparisonFinMatrix D *
      ((originalSlaterMatrixFin D)ᴴ*originalSlaterMatrixFin D)) =
    originalCopyRootDiagonal D *
      TorusLean.M2.complexify
        (OAI.Laughlin.Certificate.MatrixCompute.compressed D
          (integerFourErrorMatrix D) (OAI.Laughlin.Certificate.gramRational D)) *
      originalCopyRootDiagonal D := by
  rw [originalSlaterMatrix_gram, original_four_comparison_matrix_expansion]
  rw [four_gram_sandwich_sub_algebra, original_four_middle_complex_identity]
  simp only [TorusLean.M2.complexify,
    OAI.Laughlin.Certificate.MatrixCompute.compressed, Matrix.map_mul]

#print axioms original_four_compression_identity
end TorusLean.Shared.FermionLocalJet.FourCoupling
