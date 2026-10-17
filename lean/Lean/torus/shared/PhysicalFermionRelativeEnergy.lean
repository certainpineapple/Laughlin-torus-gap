import torus.shared.PhysicalFermionHighTail

/-! All-degree original charge-three relative removal energy. This auxiliary
interface retains even degrees as well as the high negative odd tail. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionHighTail
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.PlaneJetTailBudget
open TorusLean.Fermion.LatticePacking
open scoped BigOperators

private theorem cellMeasure_three_eq_two (G : Geometry) :
    cellMeasure G 3 = ENNReal.ofReal (3/2 : ℝ) • cellMeasure G 2 := by
  unfold cellMeasure
  rw [smul_smul, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3/2)]
  exact congrArg (fun c : ℝ => ENNReal.ofReal c • volume.restrict (cell G))
    (by push_cast; ring)

/-- Genuine same-H bound for every d, including zero and even d, in the
original mu3 measure. The threshold and constant do not depend on particles. -/
theorem paperRelativeRemoval_integrated_bound_mu3 (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (d : ℕ) (x : Space (physicalQ G theta)) :
    Integrable (fun R => occupationNormSq (physicalQ G theta)
      (paperRelativeRemoval G theta d R x)) (cellMeasure G 3) ∧
    (∫ R, occupationNormSq (physicalQ G theta)
      (paperRelativeRemoval G theta d R x) ∂cellMeasure G 3) ≤
      (3/2 : ℝ) * jetNormBudget G theta d * (d+1) *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  have h := paperRelativeRemoval_integrated_bound G theta hG d x
  rw [cellMeasure_three_eq_two]
  refine ⟨h.1.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3/2),
    smul_eq_mul]
  calc
    _ ≤ (3/2 : ℝ) * (jetNormBudget G theta d * (d+1) *
        (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re) :=
      mul_le_mul_of_nonneg_left h.2 (by norm_num)
    _ = _ := by ring

#print axioms paperRelativeRemoval_integrated_bound_mu3
end TorusLean.Shared.PhysicalFermionHighTail
