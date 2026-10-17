import torus.shared.FermionLocalJetFourCouplingOriginalComparisonCore
import torus.shared.FermionLocalJetFourCouplingTarget

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

theorem certificateFourEnergy_le_original_target_of_pointwise (G : Geometry) (theta : Twist)
    (hpoint : ∀ (d : Fin 23) (R : ℂ) (x : Space (physicalQ G theta)),
    (∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      certificateFourMatrix (d.val+1) r.val.val s.val.val *
        occupationInner (physicalQ G theta)
          (coupledFourAmplitude G theta (d.val+1) r R x)
          (coupledFourAmplitude G theta (d.val+1) s R x)).re ≤
      2 * occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) (targetMode d.val) R x) +
      (3/1000000:ℝ) * ∑ r : OddMode (d.val+1), occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x) )
    (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * coupledFourEnergy G theta x := by
  let A (R : ℂ) := ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
    (coupledFourAmplitude G theta (d.val+1) (targetMode d.val) R x)
  let B (R : ℂ) := ∑ d : Fin 23, ∑ r : OddMode (d.val+1),
    occupationNormSq (physicalQ G theta) (coupledFourAmplitude G theta (d.val+1) r R x)
  have hA : Integrable A (cellMeasure G 2) :=
    integrable_finsetSum _ (fun d _ =>
      coupledFourAmplitude_normSq_integrable G theta (d.val+1) 2 (targetMode d.val) x)
  have hB : Integrable B (cellMeasure G 2) :=
    integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun r _ =>
      coupledFourAmplitude_normSq_integrable G theta (d.val+1) 2 r x))
  have hE : Integrable (fun R => (originalFourEDDensity G theta R x).re)
      (cellMeasure G 2) := by
    have hc : Integrable (fun R => originalFourEDDensity G theta R x)
        (cellMeasure G 2) := by
      unfold originalFourEDDensity
      apply integrable_finsetSum
      intro d hd
      apply integrable_finsetSum
      intro r hr
      apply integrable_finsetSum
      intro s hs
      exact (continuous_integrable_cellMeasure G 2
        (originalFourCross_continuous G theta (d.val+1) r s x)).const_mul _
    simpa only [RCLike.re_eq_complex_re] using hc.re
  have hpoint (R : ℂ) :
      (originalFourEDDensity G theta R x).re ≤ 2*A R+(3/1000000:ℝ)*B R := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (d : Fin 23) _ =>
      hpoint d R x)
    simpa only [originalFourEDDensity,Complex.re_sum,A,B,
      Finset.sum_add_distrib,← Finset.mul_sum] using h
  calc
    certificateFourEnergy G theta x =
        ∫ R, (originalFourEDDensity G theta R x).re ∂cellMeasure G 2 :=
      certificateFourEnergy_eq_ED_density G theta x
    _ ≤ ∫ R, 2*A R+(3/1000000:ℝ)*B R ∂cellMeasure G 2 :=
      integral_mono hE ((hA.const_mul 2).add (hB.const_mul _)) hpoint
    _ = 2*(∫ R, A R ∂cellMeasure G 2) +
        (3/1000000:ℝ)*(∫ R, B R ∂cellMeasure G 2) := by
      rw [integral_add (hA.const_mul 2) (hB.const_mul _),
        integral_const_mul,integral_const_mul]
    _ = _ := by
      rw [show 2*(∫ R, A R ∂cellMeasure G 2) =
          ∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
            (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4 from
          target_copy_energy G theta x]
      rfl

theorem certificateFourEnergy_le_original_target_same_H_of_pointwise (G : Geometry) (theta : Twist)
    (hpoint : ∀ (d : Fin 23) (R : ℂ) (x : Space (physicalQ G theta)),
    (∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      certificateFourMatrix (d.val+1) r.val.val s.val.val *
        occupationInner (physicalQ G theta)
          (coupledFourAmplitude G theta (d.val+1) r R x)
          (coupledFourAmplitude G theta (d.val+1) s R x)).re ≤
      2 * occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) (targetMode d.val) R x) +
      (3/1000000:ℝ) * ∑ r : OddMode (d.val+1), occupationNormSq (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x) )
    (hG : 1≤systole G) (x : Space (physicalQ G theta)) :
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * (1222*(1+e24 G theta)^2 *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re) :=
  (certificateFourEnergy_le_original_target_of_pointwise G theta hpoint x).trans
    (add_le_add
      (le_refl (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4))
      (mul_le_mul_of_nonneg_left
        (coupledFourEnergy_same_H_bound G theta hG x) (by norm_num)))


#print axioms certificateFourEnergy_le_original_target_of_pointwise
#print axioms certificateFourEnergy_le_original_target_same_H_of_pointwise
end TorusLean.Shared.FermionLocalJet.FourCoupling
