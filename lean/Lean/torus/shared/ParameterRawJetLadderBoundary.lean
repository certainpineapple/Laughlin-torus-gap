import torus.shared.ParameterRawJetLadderBasic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Geometry TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.GroundJetReproducing TorusLean.Shared.PlaneJetMagneticPhase
open scoped ComplexConjugate

/-- The original physical section's stripped factor has the same magnetic
translation eigencharacter; this is derived by cancelling its nonzero Gaussian. -/
theorem canonicalRawStripped_lattice_translate (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (p : ℤ × ℤ) :
    translatedStrippedFactor (latticePeriod G.omega1 G.omega2 p)
      (canonicalRawStripped G theta h) =
      fun z => latticeChi G.M theta.theta1 theta.theta2 p * canonicalRawStripped G theta h z := by
  funext z
  apply mul_left_cancel₀ (gaussianFactor_ne_zero 1 z)
  rw [← magneticTranslate_stripped_factor _ _ _ (canonicalRawStripped_factor G theta h)]
  have hb := congrFun (h.property.2 p) z
  simp only [pow_one, Nat.cast_one] at hb
  rw [hb, canonicalRawStripped_factor G theta h]
  ring

/-- The entire centered factor has the original primal multiplier, which
is independent of the local derivative variable. -/
theorem canonical_centered_factor_add_period (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (p : ℤ × ℤ) (R : ℂ) :
    translatedStrippedFactor (-(R+latticePeriod G.omega1 G.omega2 p))
      (canonicalRawStripped G theta h) = fun z =>
      (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹ *
        Complex.exp (magneticExponent 1 R (latticePeriod G.omega1 G.omega2 p)) *
        translatedStrippedFactor (-R) (canonicalRawStripped G theta h) z := by
  let L := latticePeriod G.omega1 G.omega2 p
  let c := latticeChi G.M theta.theta1 theta.theta2 p
  have hc := translatedStrippedFactor_comp (-(R+L)) L (canonicalRawStripped G theta h)
  rw [canonicalRawStripped_lattice_translate, translatedStrippedFactor_const_mul] at hc
  have harg : -(R+L)+L = -R := by ring
  rw [harg] at hc
  have hphase : magneticCocycle 1 (-(R+L)) L = Complex.exp (magneticExponent 1 R L) := by
    unfold magneticCocycle magneticExponent
    simp only [map_neg, map_add, Complex.ofReal_one, one_mul]
    congr 1
    ring
  rw [hphase] at hc
  funext z
  apply mul_left_cancel₀ (latticeChi_ne_zero G.M theta.theta1 theta.theta2 p)
  calc
    _ = Complex.exp (magneticExponent 1 R L) *
      translatedStrippedFactor (-R) (canonicalRawStripped G theta h) z := congrFun hc z
    _ = _ := by
      dsimp [c, L]
      field_simp [latticeChi_ne_zero G.M theta.theta1 theta.theta2 p]

/-- Every raw coefficient level has the same original all-period parameter
boundary law, derived without differentiating an infinite periodizer. -/
theorem rawJetCoefficient_hasLatticeBoundary (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (j : ℕ) :
    HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (fun R => rawJetCoefficient G theta h j R) := by
  apply (latticeBoundary_iff_forward _ _ _ _ _ _ _).mpr
  intro p R
  change iteratedDeriv j (translatedStrippedFactor (-(R+latticePeriod G.omega1 G.omega2 p))
      (canonicalRawStripped G theta h)) 0 / (Real.sqrt (j.factorial:ℝ):ℂ) = _
  rw [canonical_centered_factor_add_period, iteratedDeriv_const_mul_field]
  simp only [pow_one, rawJetCoefficient]
  ring

theorem dualRawJetScalar_hasDualBoundary (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (j : ℕ) :
    HasDualBoundary G theta 1 (dualRawJetScalar G theta h j) := by
  unfold HasDualBoundary
  simp_rw [dualRawJetScalar_eq_conj, Complex.conj_conj]
  exact rawJetCoefficient_hasLatticeBoundary G theta h j

end TorusLean.Shared.ParameterRawJetLadder
