import torus.shared.FermionLocalJetFourCouplingPhysicalPointwiseTransport
import torus.shared.FermionLocalJetFourCouplingFiniteComparison
import torus.shared.FermionLocalJetFourCouplingOriginalSlater

/-! The actual whole-Fock comparison at one cell point, obtained by raw
exterior insertion and its genuine occupation adjoint. No source isometry,
copy independence, Gram inverse, or pointwise positivity of K-E is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock Matrix
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open scoped BigOperators ComplexConjugate ComplexOrder

theorem original_four_pointwise (G : Geometry) (theta : Twist) (d : Fin 23)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    (∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      certificateFourMatrix (d.val+1) r.val.val s.val.val *
        occupationInner (physicalQ G theta)
          (coupledFourAmplitude G theta (d.val+1) r R x)
          (coupledFourAmplitude G theta (d.val+1) s R x)).re ≤
      2 * occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) (targetMode d.val) R x) +
      (3/1000000:ℝ) * ∑ r : OddMode (d.val+1), occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x) := by
  exact original_four_pointwise_of_source_and_certificate G theta d
    (original_coupled_slater d) (original_four_comparison_certificate d) R x

#print axioms original_four_pointwise
end TorusLean.Shared.FermionLocalJet.FourCoupling
