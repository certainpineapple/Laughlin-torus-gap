import torus.shared.FermionLocalJetFourCouplingOriginalComparisonTransport
import torus.shared.FermionLocalJetFourCouplingPhysicalPointwise

/-! Original K4 <= original T4 + epsilon R4 on the whole physical Fock
carrier. The finite COM reindexing retains every D=1,...,23 and all same-D
r,s cross terms. Target d=D-1 is exactly 0,...,22. The original row support
T<=23 and D<=T have already excluded larger D in the exact E_D identity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionM1NearProjectionPhysical TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

theorem certificateFourEnergy_le_original_target (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * coupledFourEnergy G theta x := by
  exact certificateFourEnergy_le_original_target_of_pointwise G theta (original_four_pointwise G theta) x

theorem certificateFourEnergy_le_original_target_same_H (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * (1222*(1+e24 G theta)^2 *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re) := by
  exact certificateFourEnergy_le_original_target_same_H_of_pointwise G theta (original_four_pointwise G theta) hG x

#print axioms originalFourCross_continuous
#print axioms certificateFourEnergy_eq_ED_density
#print axioms certificateFourEnergy_le_original_target
#print axioms certificateFourEnergy_le_original_target_same_H
end TorusLean.Shared.FermionLocalJet.FourCoupling
