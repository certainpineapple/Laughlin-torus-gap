import torus.shared.ThermalCoherentFermionJetWord
import torus.shared.BosonAnchoredSeedActions

/-! Actual charge-k parameter actions on ordered exterior jet words.
Only the generic scalar parameter finite-sum rules from the earlier module
are reused. The finite coefficients are true exterior occupation coefficients.
Every source label is Nat, with no artificial top-mode truncation. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterRawJetWord TorusLean.Shared.BosonAnchoredSeedActions
open scoped BigOperators ContDiff

theorem exteriorWordDual_raise (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (j : Fin k → ℕ)
    (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (exteriorWordDual G theta k q j) R =
      ∑ i, (Real.sqrt ((j i)+1:ℝ):ℂ)*exteriorWordDual G theta k q (Function.update j i (j i+1)) R := by
  rw [exteriorWordDual_expansion]
  rw [parameterRaise_sum _ _ _ (fun w _ =>
    ((rawWord_contDiff G theta k _ _).differentiable (by simp)).const_mul _)]
  simp_rw [parameterRaise_const_mul k _ _ ((rawWord_contDiff G theta k _ _).differentiable (by simp))]
  rw [Finset.mul_sum]
  calc
    _ = ∑ w : Fin k → Fin (physicalQ G theta+1), ∑ i : Fin k,
        occupationInner (physicalQ G theta) q (coordinateExteriorWord (physicalQ G theta) k w) *
          ((Real.sqrt ((j i)+1:ℝ):ℂ) * rawWord G theta k (fun a => orbitalBasis G theta (physicalIndexEquiv G theta (w a)))
            (Function.update j i ((j i)+1)) R) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [show (Real.sqrt (k:ℝ):ℂ)*(occupationInner (physicalQ G theta) q (coordinateExteriorWord (physicalQ G theta) k w)*
        parameterRaise k (rawWord G theta k (fun a => orbitalBasis G theta (physicalIndexEquiv G theta (w a))) j) R) =
        occupationInner (physicalQ G theta) q (coordinateExteriorWord (physicalQ G theta) k w)*((Real.sqrt (k:ℝ):ℂ)*
        parameterRaise k (rawWord G theta k (fun a => orbitalBasis G theta (physicalIndexEquiv G theta (w a))) j) R) by ring,
        rawWord_raise, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [rawWord_update]
      push_cast
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [exteriorWordDual_expansion, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring

theorem exteriorWordDual_lower (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Space (physicalQ G theta)) (j : Fin k → ℕ)
    (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterLower k (exteriorWordDual G theta k q j) R =
      ∑ i, (Real.sqrt ((j i):ℝ):ℂ)*exteriorWordDual G theta k q (Function.update j i (j i-1)) R := by
  rw [exteriorWordDual_expansion]
  rw [parameterLower_sum _ _ _ (fun w _ =>
    ((rawWord_contDiff G theta k _ _).differentiable (by simp)).const_mul _)]
  simp_rw [parameterLower_const_mul k _ _ ((rawWord_contDiff G theta k _ _).differentiable (by simp))]
  rw [Finset.mul_sum]
  calc
    _ = ∑ w : Fin k → Fin (physicalQ G theta+1), ∑ i : Fin k,
        occupationInner (physicalQ G theta) q (coordinateExteriorWord (physicalQ G theta) k w) *
          ((Real.sqrt ((j i):ℝ):ℂ) * rawWord G theta k (fun a => orbitalBasis G theta (physicalIndexEquiv G theta (w a)))
            (Function.update j i ((j i)-1)) R) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [show (Real.sqrt (k:ℝ):ℂ)*(occupationInner (physicalQ G theta) q (coordinateExteriorWord (physicalQ G theta) k w)*
        parameterLower k (rawWord G theta k (fun a => orbitalBasis G theta (physicalIndexEquiv G theta (w a))) j) R) =
        occupationInner (physicalQ G theta) q (coordinateExteriorWord (physicalQ G theta) k w)*((Real.sqrt (k:ℝ):ℂ)*
        parameterLower k (rawWord G theta k (fun a => orbitalBasis G theta (physicalIndexEquiv G theta (w a))) j) R) by ring,
        rawWord_lower, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [rawWord_update]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [exteriorWordDual_expansion, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring

#print axioms exteriorWordDual_raise
#print axioms exteriorWordDual_lower

end TorusLean.Shared.ThermalCoherentFermionJetWord
