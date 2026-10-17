import torus.shared.FermionLocalJetFourCouplingEDIntegral

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
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionM1NearProjectionPhysical TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

def originalFourEDDensity (G : Geometry) (theta : Twist)
    (R : ℂ) (x : Space (physicalQ G theta)) : ℂ :=
  ∑ d : Fin 23, ∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
    certificateFourMatrix (d.val+1) r.val.val s.val.val *
      occupationInner (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x)
        (coupledFourAmplitude G theta (d.val+1) s R x)

theorem originalFourCross_continuous (G : Geometry) (theta : Twist)
    (D : ℕ) (r s : OddMode D) (x : Space (physicalQ G theta)) :
    Continuous (fun R => occupationInner (physicalQ G theta)
      (coupledFourAmplitude G theta D r R x) (coupledFourAmplitude G theta D s R x)) := by
  unfold occupationInner
  exact continuous_finsetSum _ (fun A _ =>
    (coupledFourAmplitude_coordinate_continuous G theta D r x A).star.mul
      (coupledFourAmplitude_coordinate_continuous G theta D s x A))

#print axioms originalFourCross_continuous

theorem certificateFourEnergy_eq_ED_density (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x =
      ∫ R, (originalFourEDDensity G theta R x).re ∂cellMeasure G 2 := by
  have hi (d : Fin 23) (r s : OddMode (d.val+1)) :
      Integrable (fun R => certificateFourMatrix (d.val+1) r.val.val s.val.val *
        occupationInner (physicalQ G theta)
          (coupledFourAmplitude G theta (d.val+1) r R x)
          (coupledFourAmplitude G theta (d.val+1) s R x)) (cellMeasure G 2) :=
    (continuous_integrable_cellMeasure G 2
      (originalFourCross_continuous G theta (d.val+1) r s x)).const_mul _
  have hsum : Integrable (fun R => originalFourEDDensity G theta R x)
      (cellMeasure G 2) := by
    unfold originalFourEDDensity
    exact integrable_finsetSum Finset.univ (fun d _ =>
      integrable_finsetSum Finset.univ (fun r _ =>
        integrable_finsetSum Finset.univ (fun s _ => hi d r s)))
  have hre : (∫ R, (originalFourEDDensity G theta R x).re ∂cellMeasure G 2) =
      (∫ R, originalFourEDDensity G theta R x ∂cellMeasure G 2).re := integral_re hsum
  rw [certificateFourEnergy_eq_ED_integrals,hre]
  congr 1
  unfold originalFourEDDensity
  rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ => hi d r s)))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ => hi d r s))]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integral_finsetSum _ (fun s _ => hi d r s)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_const_mul]
  rfl


#print axioms certificateFourEnergy_eq_ED_density
end TorusLean.Shared.FermionLocalJet.FourCoupling
