import torus.shared.FermionLocalJetFourCouplingSlaterGram
import torus.shared.FermionLocalJetFourCouplingIntegerError
import Mathlib.Tactic.NoncommRing
import FermionM3Data

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

def fourCertificateDiagonal (D : ℕ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℂ :=
  Matrix.diagonal (fun i =>
    (((if 2*i.val+1=1 then 2 else 0)+(3/1000000:ℚ):ℚ):ℂ))

def fourComparisonFinMatrix (D : ℕ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℂ :=
  fourCertificateDiagonal D -
    Matrix.of (fun (i j : Fin ((D+1)/2)) =>
      certificateFourMatrix D (2*i.val+1) (2*j.val+1))

theorem fourComparisonFinMatrix_hermitian (D : ℕ) :
    (fourComparisonFinMatrix D).IsHermitian := by
  change (fourCertificateDiagonal D -
    Matrix.of (fun (i j : Fin ((D+1)/2)) =>
      certificateFourMatrix D (2*i.val+1) (2*j.val+1))).IsHermitian
  have hdiag : (fourCertificateDiagonal D).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact star_ratCast _
  have herr :
      (Matrix.of (fun (i j : Fin ((D+1)/2)) =>
        certificateFourMatrix D (2*i.val+1) (2*j.val+1))).IsHermitian :=
    Matrix.IsHermitian.ext (fun i j =>
      certificateFourMatrix_hermitian D (2*i.val+1) (2*j.val+1))
  exact Matrix.IsHermitian.sub hdiag herr

#print axioms fourComparisonFinMatrix_hermitian
end TorusLean.Shared.FermionLocalJet.FourCoupling
