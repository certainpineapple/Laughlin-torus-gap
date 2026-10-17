import torus.shared.MagneticCellUnfolding
import torus.geometry.Periodization
import CanonicalPlaneJets
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! One-edge unfolding for genuine continuous magnetic sections. Analytic
LLL membership is not required of the exterior rank coefficient. All bounds
and integral domains are derived from the original full boundary law. -/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared.MagneticBoundaryUnfolding

open Set MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open scoped ComplexConjugate ENNReal Topology

/-- The actual section norm is periodic for every original lattice period. -/
theorem boundarySection_norm_add_period (G : Geometry) (theta : Twist) (k : ℕ)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 h) (p : ℤ × ℤ) (z : ℂ) :
    ‖h (z + latticePeriod G.omega1 G.omega2 p)‖ = ‖h z‖ := by
  have hb := (latticeBoundary_iff_forward G.M k G.omega1 G.omega2
    theta.theta1 theta.theta2 h).mp hb p z
  rw [hb]
  simp only [norm_mul, norm_inv, norm_pow, latticeChi_norm,
    magneticMultiplier_norm, one_pow, inv_one, one_mul]

/-- A global norm bound derived from the actual cell and section predicates.
It contains no physical finite-rank or periodized-jet norm assumption. -/
theorem boundarySection_global_norm_bound (G : Geometry) (theta : Twist) (k : ℕ)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 h) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖h z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedCell G).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z
  calc
    ‖h z‖ = ‖h (cellRemainder G z +
        latticePeriod G.omega1 G.omega2 (cellTileIndex G z))‖ :=
      congrArg (fun w : ℂ => ‖h w‖) (cell_decomposition G z)
    _ = ‖h (cellRemainder G z)‖ :=
      boundarySection_norm_add_period G theta k h hc hb (cellTileIndex G z) (cellRemainder G z)
    _ ≤ max C 0 := (hC _ (cell_subset_closedCell G (cellRemainder_mem G z))).trans
      (le_max_left _ _)

/-- The actual section times any plane-L1 seed is plane integrable. -/
theorem boundarySection_seed_cross_integrable (G : Geometry) (theta : Twist) (k : ℕ)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 h) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    Integrable (fun z => conj (h z) * f z) planeMeasure := by
  obtain ⟨C, _hC, hbound⟩ := boundarySection_global_norm_bound G theta k h hc hb
  apply hf.bdd_mul (c := C) ((Complex.continuous_conj.comp
    hc).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Function.comp_apply, Complex.norm_conj] using hbound z

/-- Exact cancellation with the original inverse chi and magnetic phase.
The remaining integrand is the actual plane cross product at z-period(p). -/
theorem magneticImage_cross_pointwise (G : Geometry) (theta : Twist) (k : ℕ)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 h) (f : ℂ → ℂ) (p : ℤ × ℤ) (z : ℂ) :
    conj (h z) * magneticImage G.M k G.omega1 G.omega2
      theta.theta1 theta.theta2 f p z =
      conj (h (z - latticePeriod G.omega1 G.omega2 p)) *
        f (z - latticePeriod G.omega1 G.omega2 p) := by
  have hn : ‖latticeChi G.M theta.theta1 theta.theta2 p ^ k‖ = 1 := by
    rw [norm_pow, latticeChi_norm, one_pow]
  have hb := congrFun (hb p) z
  calc
    _ = conj (latticeChi G.M theta.theta1 theta.theta2 p ^ k * h z) *
        magneticTranslate (k : ℝ) (latticePeriod G.omega1 G.omega2 p) f z := by
      rw [magneticImage, Complex.inv_eq_conj hn, map_mul]
      ring
    _ = conj (magneticTranslate (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
        h z) * magneticTranslate (k : ℝ)
          (latticePeriod G.omega1 G.omega2 p) f z := by rw [hb]
    _ = _ := magnetic_cross_pointwise (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
      z h f

/-- Every actual charge-one image cross product is integrable in μ1. -/
theorem magneticImage_cross_integrable_cell (G : Geometry) (theta : Twist)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 h) (f : ℂ → ℂ) (hf : Integrable f planeMeasure)
    (p : ℤ × ℤ) :
    Integrable (fun z => conj (h z) * magneticImage G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f p z) (cellMeasure G 1) := by
  have hi := (planeMeasure_translate (latticePeriod G.omega1 G.omega2 p)).integrable_comp_of_integrable
    (boundarySection_seed_cross_integrable G theta 1 h hc hb f hf)
  have hcell : Integrable (fun z =>
      conj (h (z - latticePeriod G.omega1 G.omega2 p)) *
        f (z - latticePeriod G.omega1 G.omega2 p)) (planeMeasure.restrict (cell G)) :=
    hi.mono_measure Measure.restrict_le_self
  rw [show planeMeasure.restrict (cell G) = cellMeasure G 1 from
    normalizedPlane_restrict_cell G] at hcell
  exact hcell.congr (Filter.Eventually.of_forall fun z =>
    (magneticImage_cross_pointwise G theta 1 h hc hb f p z).symm)

/-- Absolute integral summability is derived from the seed domain and the
actual tiling, rather than assumed as a raw-jet norm budget. -/
theorem summable_magneticImage_cross_cellIntegral_norm (G : Geometry) (theta : Twist)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 h) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    Summable (fun p : ℤ × ℤ => ∫ z,
      ‖conj (h z) * magneticImage G.M 1 G.omega1 G.omega2
        theta.theta1 theta.theta2 f p z‖ ∂cellMeasure G 1) := by
  have hs := summable_cellIntegral_norm G (fun z => conj (h z) * f z)
    (boundarySection_seed_cross_integrable G theta 1 h hc hb f hf)
  have hsneg := hs.comp_injective (neg_injective :
    Function.Injective (fun p : ℤ × ℤ => -p))
  simp only [Function.comp_def, latticePeriod_neg, ← sub_eq_add_neg] at hsneg
  apply hsneg.congr
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    congrArg norm (magneticImage_cross_pointwise G theta 1 h hc hb f p z).symm

/-- The actual image cell integrals sum to the original plane cross integral. -/
theorem tsum_magneticImage_cellInner_eq_planeInner (G : Geometry) (theta : Twist)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 h) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    (∑' p : ℤ × ℤ, ∫ z, conj (h z) * magneticImage G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f p z ∂cellMeasure G 1) = planeInner h f := by
  calc
    _ = ∑' p : ℤ × ℤ, ∫ z,
        conj (h (z - latticePeriod G.omega1 G.omega2 p)) *
          f (z - latticePeriod G.omega1 G.omega2 p) ∂cellMeasure G 1 := by
      apply tsum_congr
      intro p
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => magneticImage_cross_pointwise G theta 1 h hc hb f p z
    _ = ∑' p : ℤ × ℤ, ∫ z,
        conj (h (z + latticePeriod G.omega1 G.omega2 p)) *
          f (z + latticePeriod G.omega1 G.omega2 p) ∂cellMeasure G 1 := by
      simpa only [Equiv.neg_apply, latticePeriod_neg, ← sub_eq_add_neg] using
        (Equiv.neg (ℤ × ℤ)).tsum_eq (fun p : ℤ × ℤ => ∫ z,
          conj (h (z + latticePeriod G.omega1 G.omega2 p)) *
            f (z + latticePeriod G.omega1 G.omega2 p) ∂cellMeasure G 1)
    _ = _ := tsum_cellIntegral_eq_planeIntegral G (fun z => conj (h z) * f z)
      (boundarySection_seed_cross_integrable G theta 1 h hc hb f hf)

/-- The periodized cross product itself has the correct actual cell L1 domain. -/
theorem magneticPeriodization_cross_integrable_cell (G : Geometry) (theta : Twist)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 h) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    Integrable (fun z => conj (h z) * magneticPeriodization G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f z) (cellMeasure G 1) := by
  let F : (ℤ × ℤ) → ℂ → ℂ := fun p z => conj (h z) * magneticImage
    G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 f p z
  have hF (p : ℤ × ℤ) : Integrable (F p) (cellMeasure G 1) :=
    magneticImage_cross_integrable_cell G theta h hc hb f hf p
  have hu := boundarySection_seed_cross_integrable G theta 1 h hc hb f hf
  have hl : (∑' p : ℤ × ℤ, ∫⁻ z, ‖F p z‖ₑ ∂cellMeasure G 1) =
      ∫⁻ z, ‖conj (h z) * f z‖ₑ ∂planeMeasure := by
    calc
      _ = ∑' p : ℤ × ℤ, ∫⁻ z,
          ‖conj (h (z - latticePeriod G.omega1 G.omega2 p)) *
            f (z - latticePeriod G.omega1 G.omega2 p)‖ₑ ∂cellMeasure G 1 := by
        apply tsum_congr
        intro p
        apply lintegral_congr
        intro z
        exact congrArg enorm (magneticImage_cross_pointwise G theta 1 h hc hb f p z)
      _ = ∑' p : ℤ × ℤ, ∫⁻ z,
          ‖conj (h (z + latticePeriod G.omega1 G.omega2 p)) *
            f (z + latticePeriod G.omega1 G.omega2 p)‖ₑ ∂cellMeasure G 1 := by
        simpa only [Equiv.neg_apply, latticePeriod_neg, ← sub_eq_add_neg] using
          (Equiv.neg (ℤ × ℤ)).tsum_eq (fun p : ℤ × ℤ => ∫⁻ z,
            ‖conj (h (z + latticePeriod G.omega1 G.omega2 p)) *
              f (z + latticePeriod G.omega1 G.omega2 p)‖ₑ ∂cellMeasure G 1)
      _ = _ := tsum_cellLIntegral_eq_planeLIntegral G (fun z => ‖conj (h z) * f z‖ₑ)
  have htsum : Integrable (fun z => ∑' p : ℤ × ℤ, F p z) (cellMeasure G 1) := by
    refine ⟨(AEMeasurable.tsum fun p => (hF p).aemeasurable).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum (fun p => (hF p).aestronglyMeasurable.enorm), hl]
    exact hu.hasFiniteIntegral
  simpa only [F, magneticPeriodization, tsum_mul_left] using htsum

/-- Actual magnetic inner unfolding, with only the seed's plane-L1 domain
as a premise. No LLL membership of the periodized seed is assumed. -/
theorem cellInner_magneticPeriodization_eq_planeInner (G : Geometry) (theta : Twist)
    (h : ℂ → ℂ) (hc : Continuous h)
    (hb : HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 h) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    cellInner G 1 h (magneticPeriodization G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f) = planeInner h f := by
  have hi := integral_tsum_of_summable_integral_norm
    (magneticImage_cross_integrable_cell G theta h hc hb f hf)
    (summable_magneticImage_cross_cellIntegral_norm G theta h hc hb f hf)
  calc
    _ = ∫ z, ∑' p : ℤ × ℤ, conj (h z) * magneticImage G.M 1 G.omega1 G.omega2
        theta.theta1 theta.theta2 f p z ∂cellMeasure G 1 := by
      simp only [cellInner, magneticPeriodization, tsum_mul_left]
    _ = ∑' p : ℤ × ℤ, ∫ z, conj (h z) * magneticImage G.M 1 G.omega1 G.omega2
        theta.theta1 theta.theta2 f p z ∂cellMeasure G 1 := hi.symm
    _ = _ := tsum_magneticImage_cellInner_eq_planeInner G theta h hc hb f hf


end TorusLean.Shared.MagneticBoundaryUnfolding
