import torus.shared.BosonPeriodizedSeedNat
import torus.shared.BosonAnchoredSeedActions
import torus.shared.ThermalCoherentSeedDomain

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredNatActions
open TorusLean.Boson TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.ParameterRawJetWord
open TorusLean.Shared.ThermalCoherentSeedWord TorusLean.Shared.BosonAnchoredSeedActions
open scoped BigOperators ContDiff

def wordDualNat (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → ℕ) (R : ℂ) : ℂ :=
  occupationInner (fun _ => 1) q (anchoredSeedNat G theta R (canonicalWord k j))

theorem wordDualNat_expansion (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → ℕ) :
    wordDualNat G theta k q j = fun R => ∑ w : Fin k → OrbitalIndex G theta,
      occupationInner (fun _ => 1) q (canonicalWord k w) *
        rawWord G theta k (fun a => orbitalBasis G theta (w a)) j R := by
  funext R
  exact anchoredSeedNat_word_dual_expansion G theta k j q R

theorem wordDualNat_contDiff (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → ℕ) :
    ContDiff ℝ ∞ (wordDualNat G theta k q j) := by
  rw [wordDualNat_expansion]
  apply ContDiff.sum
  intro w hw
  exact contDiff_const.mul (rawWord_contDiff G theta k _ _)

theorem wordDualNat_boundary (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → ℕ) :
    HasDualBoundary G theta k (wordDualNat G theta k q j) := by
  rw [wordDualNat_expansion]
  exact ThermalCoherentSeedDomain.hasDualBoundary_finset_linear G theta k Finset.univ _ _
    (fun w _ => rawWord_hasDualBoundary G theta k _ _)

theorem wordDualNat_raise (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → ℕ)
    (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (wordDualNat G theta k q j) R =
      ∑ i, (Real.sqrt ((j i)+1:ℝ):ℂ)*wordDualNat G theta k q (Function.update j i (j i+1)) R := by
  rw [wordDualNat_expansion]
  rw [parameterRaise_sum _ _ _ (fun w _ =>
    ((rawWord_contDiff G theta k _ _).differentiable (by simp)).const_mul _)]
  simp_rw [parameterRaise_const_mul k _ _ ((rawWord_contDiff G theta k _ _).differentiable (by simp))]
  rw [Finset.mul_sum]
  calc
    _ = ∑ w : Fin k → OrbitalIndex G theta, ∑ i : Fin k,
        occupationInner (fun _ => 1) q (canonicalWord k w) *
          ((Real.sqrt ((j i)+1:ℝ):ℂ) * rawWord G theta k (fun a => orbitalBasis G theta (w a))
            (Function.update j i ((j i)+1)) R) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [show (Real.sqrt (k:ℝ):ℂ)*(occupationInner (fun _ => 1) q (canonicalWord k w)*
        parameterRaise k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) j) R) =
        occupationInner (fun _ => 1) q (canonicalWord k w)*((Real.sqrt (k:ℝ):ℂ)*
        parameterRaise k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) j) R) by ring,
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
      rw [wordDualNat_expansion, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring

theorem wordDualNat_lower (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Core (OrbitalIndex G theta) ℂ) (j : Fin k → ℕ)
    (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterLower k (wordDualNat G theta k q j) R =
      ∑ i, (Real.sqrt ((j i):ℝ):ℂ)*wordDualNat G theta k q (Function.update j i (j i-1)) R := by
  rw [wordDualNat_expansion]
  rw [parameterLower_sum _ _ _ (fun w _ =>
    ((rawWord_contDiff G theta k _ _).differentiable (by simp)).const_mul _)]
  simp_rw [parameterLower_const_mul k _ _ ((rawWord_contDiff G theta k _ _).differentiable (by simp))]
  rw [Finset.mul_sum]
  calc
    _ = ∑ w : Fin k → OrbitalIndex G theta, ∑ i : Fin k,
        occupationInner (fun _ => 1) q (canonicalWord k w) *
          ((Real.sqrt ((j i):ℝ):ℂ) * rawWord G theta k (fun a => orbitalBasis G theta (w a))
            (Function.update j i ((j i)-1)) R) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [show (Real.sqrt (k:ℝ):ℂ)*(occupationInner (fun _ => 1) q (canonicalWord k w)*
        parameterLower k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) j) R) =
        occupationInner (fun _ => 1) q (canonicalWord k w)*((Real.sqrt (k:ℝ):ℂ)*
        parameterLower k (rawWord G theta k (fun a => orbitalBasis G theta (w a)) j) R) by ring,
        rawWord_lower, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [rawWord_update]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [wordDualNat_expansion, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring

end TorusLean.Shared.BosonAnchoredNatActions
