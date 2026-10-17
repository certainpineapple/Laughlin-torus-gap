import torus.shared.FermionLocalJetFourCouplingFiniteComparisonMiddle

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

theorem original_four_middle_complex_identity (D : ℕ) :
    (originalCopyRootDiagonal D * fourCertificateDiagonal D * originalCopyRootDiagonal D -
      (originalCopyRootDiagonal D * originalCopyRootDiagonal D) *
        (integerFourErrorMatrix D).map (Rat.castHom ℂ) *
        (originalCopyRootDiagonal D * originalCopyRootDiagonal D)) =
      (OAI.Laughlin.Certificate.MatrixCompute.middle D (integerFourErrorMatrix D)).map
        (Rat.castHom ℂ) := by
  rw [originalCopyRoot_middle, originalCopyRootDiagonal_sq]
  simp only [OAI.Laughlin.Certificate.MatrixCompute.middle,
    Matrix.map_mul, Matrix.map_sub _ (fun a b => map_sub (Rat.castHom ℂ) a b)]
  rfl

#print axioms original_four_middle_complex_identity
end TorusLean.Shared.FermionLocalJet.FourCoupling
