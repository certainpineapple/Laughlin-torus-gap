import torus.shared.PhysicalFermionHighTail

/-! Uniform shortest-cycle quantifiers for the actual physical high odd tail.
The scalar delta is the existing UniformTail.delta applied to the actual
jetNormBudget, not a new asymptotic proxy.  No numerical L is asserted. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionHighTail
open MeasureTheory Filter Topology TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.FermionLocalJet
open TorusLean.Shared.PlaneJetTailBudget TorusLean.Fermion.LatticePacking
open TorusLean.Fermion.UniformTail
open scoped BigOperators

/-- One threshold works for ALL geometries and twists with sufficiently large
actual systole. The coefficient is exactly the physical high-jet supremum tail. -/
theorem actual_jet_tail_uniform (eps : ℝ) (heps : 0 < eps) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      |delta (jetNormBudget G theta) - (61/4096 : ℝ)| < eps := by
  let l : Filter (Geometry × Twist) :=
    Filter.comap (fun u : Geometry × Twist => systole u.1) atTop
  have hsys : Tendsto (fun u : Geometry × Twist => systole u.1) l atTop :=
    Filter.tendsto_comap
  have ht := actual_jet_tail_tendsto
    (fun u : Geometry × Twist => u.1) (fun u => u.2) hsys
  have he : ∀ᶠ u : Geometry × Twist in l,
      |delta (jetNormBudget u.1 u.2) - (61/4096 : ℝ)| < eps := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ht eps heps)
  change ∀ᶠ u : Geometry × Twist in
    Filter.comap (fun u : Geometry × Twist => systole u.1) atTop,
      |delta (jetNormBudget u.1 u.2) - (61/4096 : ℝ)| < eps at he
  have hreal : ∀ᶠ t : ℝ in atTop, ∀ u : Geometry × Twist, systole u.1 = t →
      |delta (jetNormBudget u.1 u.2) - (61/4096 : ℝ)| < eps :=
    Filter.eventually_comap.mp he
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hreal
  refine ⟨max 1 L, le_max_left _ _, ?_⟩
  intro G theta hG
  exact hL (systole G) ((le_max_right 1 L).trans hG) (G, theta) rfl

/-- Uniform asymptotic negative-tail payment by the SAME physical H, on the
entire original Fock space. In particular no particle-number loss occurs. -/
theorem physical_negative_tail_uniform (eps : ℝ) (heps : 0 < eps) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ x : Space (physicalQ G theta),
        Summable (fun m => ∫ R, ‖-edgeWeight m * occupationNormSq (physicalQ G theta)
          (paperRelativeRemoval G theta (degree m) R x)‖ ∂cellMeasure G 2) ∧
        -(((61/4096 : ℝ) + eps) *
          (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re) ≤
            negativeRelativeTailEnergy G theta x := by
  obtain ⟨L, hL1, hL⟩ := actual_jet_tail_uniform eps heps
  refine ⟨L, hL1, ?_⟩
  intro G theta hG x
  have hsys : 1 ≤ systole G := hL1.trans hG
  have htail := physical_negative_tail_same_H G theta hsys x
  have hdelta : delta (jetNormBudget G theta) ≤ (61/4096 : ℝ) + eps := by
    have h := (abs_lt.mp (hL G theta hG)).2
    linarith
  have hE : 0 ≤ (occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
    rw [← pairDescendant_same_H_energy G theta x 0]
    exact integral_nonneg (fun R => occupationNormSq_nonneg _ _)
  refine ⟨htail.1, ?_⟩
  exact (neg_le_neg (mul_le_mul_of_nonneg_right hdelta hE)).trans htail.2

/-- The same single L works simultaneously on every original exterior particle
sector. N is quantified only after L, geometry and twist; it never enters L. -/
theorem physical_negative_tail_uniform_all_particles (eps : ℝ) (heps : 0 < eps) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (N : ℕ) (x : Exterior (Fin (physicalQ G theta+1)) N),
        -(((61/4096 : ℝ) + eps) *
          (occupationInner (physicalQ G theta) (x : Space (physicalQ G theta))
            (physicalHamiltonian G theta (x : Space (physicalQ G theta)))).re) ≤
              ∫ R, ∑' m, q (degree m) * occupationNormSq (physicalQ G theta)
                (paperRelativeRemoval G theta (degree m) R
                  (x : Space (physicalQ G theta))) ∂cellMeasure G 3 := by
  obtain ⟨L, hL, hbound⟩ := physical_negative_tail_uniform eps heps
  refine ⟨L, hL, ?_⟩
  intro G theta hG N x
  rw [← negativeRelativeTailEnergy_original_mu3]
  exact (hbound G theta hG x).2

#print axioms actual_jet_tail_uniform
#print axioms physical_negative_tail_uniform
#print axioms physical_negative_tail_uniform_all_particles
end TorusLean.Shared.PhysicalFermionHighTail
