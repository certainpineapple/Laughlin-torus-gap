import torus.shared.PhysicalFermionNormalSquareIntegral

/-! The four-body term is an actual nonnegative square.  Even-pair
commutation is derived from the original contraction anti-commutation, and
all real/integral exchanges use the proved original two-cell integrability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionNormalSquare
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open scoped BigOperators ComplexConjugate

lemma vectorAnnihilate_anticomm_apply (Q : ℕ) (a b : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q a (vectorAnnihilate Q b x) =
      -(vectorAnnihilate Q b (vectorAnnihilate Q a x)) :=
  CliffordAlgebra.contractLeft_comm _ _ _

lemma rawPairAnnihilate_commute (Q : ℕ) (a b c d : Orbital Q) :
    rawPairAnnihilate Q a b * rawPairAnnihilate Q c d =
      rawPairAnnihilate Q c d * rawPairAnnihilate Q a b := by
  apply LinearMap.ext
  intro x
  simp only [rawPairAnnihilate, Module.End.mul_apply]
  rw [vectorAnnihilate_anticomm_apply Q a d, map_neg,
    vectorAnnihilate_anticomm_apply Q b d, neg_neg,
    vectorAnnihilate_anticomm_apply Q a c, map_neg, map_neg,
    vectorAnnihilate_anticomm_apply Q b c, map_neg, neg_neg]

lemma pairAt_commute (G : Geometry) (theta : Twist) (R S : ℂ) :
    pairAt G theta R * pairAt G theta S = pairAt G theta S * pairAt G theta R :=
  rawPairAnnihilate_commute _ _ _ _ _

lemma pairCreateAt_adjoint_right (G : Geometry) (theta : Twist) (R : ℂ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x (pairCreateAt G theta R y) =
      occupationInner (physicalQ G theta) (pairAt G theta R x) y := by
  have h := congrArg star (rawPairCreate_adjoint (physicalQ G theta)
    (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R) y x)
  simpa only [occupationInner_star, pairAt, pairCreateAt] using h

/-- Zero-contraction density is the literal square of two original raw-pair
annihilators, not positivity inserted as a hypothesis. -/
theorem fourBody_density_normSq (G : Geometry) (theta : Twist) (R S : ℂ)
    (x : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      ((pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) x) =
      (occupationNormSq (physicalQ G theta) (pairAt G theta S (pairAt G theta R x)) : ℂ) := by
  simp only [Module.End.mul_apply, pairCreateAt_adjoint_right]
  have h := LinearMap.congr_fun (pairAt_commute G theta R S) x
  simp only [Module.End.mul_apply] at h
  rw [h, occupationInner_self]

lemma fourBody_density_slice_integrable (G : Geometry) (theta : Twist)
    (R : ℂ) (x y : Space (physicalQ G theta)) :
    Integrable (fun S => occupationInner (physicalQ G theta) x
      ((pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) y))
      (cellMeasure G 2) := by
  change Integrable (fun S => operatorForm (physicalQ G theta) x y
    (pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S)) _
  simp_rw [fourBody_density_expansion]
  exact twoCenterExpansion_slice_integrable G theta _ R

/-- Complete four-body form equals the two-cell raw pair square in μ₂×μ₂. -/
theorem matrixFourBody_real_integral_normSq (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    (occupationInner (physicalQ G theta) x
      (matrixFourBody (physicalQ G theta) (contactMatrix G theta) x)).re =
      ∫ R, ∫ S, occupationNormSq (physicalQ G theta) (pairAt G theta S (pairAt G theta R x))
        ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  rw [matrixFourBody_integral]
  have ho := integral_re (physical_fourBody_density_integrable G theta x x).integral_prod_left
  change (∫ R, (∫ S, occupationInner (physicalQ G theta) x
    ((pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) x)
      ∂cellMeasure G 2).re ∂cellMeasure G 2) = _ at ho
  refine ho.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with R
  have hi := integral_re (fourBody_density_slice_integrable G theta R x x)
  change (∫ S, (occupationInner (physicalQ G theta) x
    ((pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) x)).re
      ∂cellMeasure G 2) = _ at hi
  refine hi.symm.trans ?_
  simp only [fourBody_density_normSq, Complex.ofReal_re]

/-- Genuine nonnegativity of the physical normal-ordered four-body term. -/
theorem matrixFourBody_nonneg (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    0 ≤ (occupationInner (physicalQ G theta) x
      (matrixFourBody (physicalQ G theta) (contactMatrix G theta) x)).re := by
  rw [matrixFourBody_real_integral_normSq]
  apply integral_nonneg
  intro R
  change (0 : ℝ) ≤ ∫ S, occupationNormSq (physicalQ G theta)
    (pairAt G theta S (pairAt G theta R x)) ∂cellMeasure G 2
  apply integral_nonneg
  intro S
  change (0 : ℝ) ≤ occupationNormSq (physicalQ G theta) (pairAt G theta S (pairAt G theta R x))
  exact occupationNormSq_nonneg _ _

#print axioms rawPairAnnihilate_commute
#print axioms pairAt_commute
#print axioms fourBody_density_normSq
#print axioms matrixFourBody_real_integral_normSq
#print axioms matrixFourBody_nonneg
end TorusLean.Shared.PhysicalFermionNormalSquare
