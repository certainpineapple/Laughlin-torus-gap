import torus.shared.FermionLocalJetFourCouplingFiniteComparisonHermitian

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

theorem originalCopyRoot_middle (D : ℕ) :
    originalCopyRootDiagonal D * fourCertificateDiagonal D * originalCopyRootDiagonal D =
      (Matrix.diagonal (fun i : Fin ((D+1)/2) =>
        ((if 2*i.val+1=1 then 2 else 0)+(3/1000000:ℚ)) *
          OAI.Laughlin.Certificate.MatrixCompute.copyWeight D i)).map (Rat.castHom ℂ) := by
  ext i j
  by_cases hij : i=j
  · subst j
    have hs := congrArg (fun A : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℂ => A i i)
      (originalCopyRootDiagonal_sq D)
    simp only [originalCopyRootDiagonal,Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq,Matrix.map_apply,Rat.coe_castHom] at hs
    simp only [originalCopyRootDiagonal,fourCertificateDiagonal,
      Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply_eq,Matrix.map_apply,Rat.coe_castHom,Rat.cast_mul]
    change _ = _ * (OAI.Laughlin.Certificate.copyWeight D i:ℂ)
    rw [← hs]
    ring
  · simp [originalCopyRootDiagonal,fourCertificateDiagonal,
      Matrix.diagonal_mul_diagonal,Matrix.map_apply,hij]


#print axioms originalCopyRoot_middle
end TorusLean.Shared.FermionLocalJet.FourCoupling
