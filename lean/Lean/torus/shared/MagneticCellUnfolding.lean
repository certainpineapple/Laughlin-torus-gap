import torus.shared.CellTiling
import torus.geometry.Periodization
import CanonicalPlaneJets
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Actual magnetic cell inner-product unfolding

An actual raw magnetic section has globally bounded norm: continuity bounds
it on the existing compact closed cell, and the actual floor decomposition
and unit-modulus boundary law extend that bound to the whole plane. The bound
is proved for each section, not supplied as an input or identified with a
quantitative cell-norm budget.

The inverse chi and magnetic multiplier cancel image by image against the
actual section boundary law. Existing cell tiling then derives absolute
integral summability, integrability of the periodized cross product, and the
physical inner-unfold identity for every plane-L1 seed. In particular the
accepted canonical plane jets and their actual magnetic translates satisfy
the seed domain, without any periodizer-LLL-membership assumption.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared.MagneticCellUnfolding

open Set MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open scoped ComplexConjugate ENNReal Topology

/-- The actual section norm is periodic for every original lattice period. -/
theorem rawLLL_norm_add_period (G : Geometry) (theta : Twist) (k : ℕ)
    (h : RawLLL G theta k) (p : ℤ × ℤ) (z : ℂ) :
    ‖h.val (z + latticePeriod G.omega1 G.omega2 p)‖ = ‖h.val z‖ := by
  have hb := (latticeBoundary_iff_forward G.M k G.omega1 G.omega2
    theta.theta1 theta.theta2 h.val).mp h.property.2 p z
  rw [hb]
  simp only [norm_mul, norm_inv, norm_pow, latticeChi_norm,
    magneticMultiplier_norm, one_pow, inv_one, one_mul]

/-- A global norm bound derived from the actual cell and section predicates.
It contains no physical finite-rank or periodized-jet norm assumption. -/
theorem rawLLL_global_norm_bound (G : Geometry) (theta : Twist) (k : ℕ)
    (h : RawLLL G theta k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖h.val z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedCell G).exists_bound_of_continuousOn
    (rawLLL_continuous G theta k h).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z
  calc
    ‖h.val z‖ = ‖h.val (cellRemainder G z +
        latticePeriod G.omega1 G.omega2 (cellTileIndex G z))‖ :=
      congrArg (fun w : ℂ => ‖h.val w‖) (cell_decomposition G z)
    _ = ‖h.val (cellRemainder G z)‖ :=
      rawLLL_norm_add_period G theta k h (cellTileIndex G z) (cellRemainder G z)
    _ ≤ max C 0 := (hC _ (cell_subset_closedCell G (cellRemainder_mem G z))).trans
      (le_max_left _ _)

/-- The actual section times any plane-L1 seed is plane integrable. -/
theorem rawLLL_seed_cross_integrable (G : Geometry) (theta : Twist) (k : ℕ)
    (h : RawLLL G theta k) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    Integrable (fun z => conj (h.val z) * f z) planeMeasure := by
  obtain ⟨C, _hC, hbound⟩ := rawLLL_global_norm_bound G theta k h
  apply hf.bdd_mul (c := C) ((Complex.continuous_conj.comp
    (rawLLL_continuous G theta k h)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Function.comp_apply, Complex.norm_conj] using hbound z

/-- Exact cancellation with the original inverse chi and magnetic phase.
The remaining integrand is the actual plane cross product at z-period(p). -/
theorem magneticImage_cross_pointwise (G : Geometry) (theta : Twist) (k : ℕ)
    (h : RawLLL G theta k) (f : ℂ → ℂ) (p : ℤ × ℤ) (z : ℂ) :
    conj (h.val z) * magneticImage G.M k G.omega1 G.omega2
      theta.theta1 theta.theta2 f p z =
      conj (h.val (z - latticePeriod G.omega1 G.omega2 p)) *
        f (z - latticePeriod G.omega1 G.omega2 p) := by
  have hn : ‖latticeChi G.M theta.theta1 theta.theta2 p ^ k‖ = 1 := by
    rw [norm_pow, latticeChi_norm, one_pow]
  have hb := congrFun (h.property.2 p) z
  calc
    _ = conj (latticeChi G.M theta.theta1 theta.theta2 p ^ k * h.val z) *
        magneticTranslate (k : ℝ) (latticePeriod G.omega1 G.omega2 p) f z := by
      rw [magneticImage, Complex.inv_eq_conj hn, map_mul]
      ring
    _ = conj (magneticTranslate (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
        h.val z) * magneticTranslate (k : ℝ)
          (latticePeriod G.omega1 G.omega2 p) f z := by rw [hb]
    _ = _ := magnetic_cross_pointwise (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
      z h.val f

/-- Every actual charge-one image cross product is integrable in μ1. -/
theorem magneticImage_cross_integrable_cell (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (f : ℂ → ℂ) (hf : Integrable f planeMeasure)
    (p : ℤ × ℤ) :
    Integrable (fun z => conj (h.val z) * magneticImage G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f p z) (cellMeasure G 1) := by
  have hi := (planeMeasure_translate (latticePeriod G.omega1 G.omega2 p)).integrable_comp_of_integrable
    (rawLLL_seed_cross_integrable G theta 1 h f hf)
  have hc : Integrable (fun z =>
      conj (h.val (z - latticePeriod G.omega1 G.omega2 p)) *
        f (z - latticePeriod G.omega1 G.omega2 p)) (planeMeasure.restrict (cell G)) :=
    hi.mono_measure Measure.restrict_le_self
  rw [show planeMeasure.restrict (cell G) = cellMeasure G 1 from
    normalizedPlane_restrict_cell G] at hc
  exact hc.congr (Filter.Eventually.of_forall fun z =>
    (magneticImage_cross_pointwise G theta 1 h f p z).symm)

/-- Absolute integral summability is derived from the seed domain and the
actual tiling, rather than assumed as a raw-jet norm budget. -/
theorem summable_magneticImage_cross_cellIntegral_norm (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    Summable (fun p : ℤ × ℤ => ∫ z,
      ‖conj (h.val z) * magneticImage G.M 1 G.omega1 G.omega2
        theta.theta1 theta.theta2 f p z‖ ∂cellMeasure G 1) := by
  have hs := summable_cellIntegral_norm G (fun z => conj (h.val z) * f z)
    (rawLLL_seed_cross_integrable G theta 1 h f hf)
  have hsneg := hs.comp_injective (neg_injective :
    Function.Injective (fun p : ℤ × ℤ => -p))
  simp only [Function.comp_def, latticePeriod_neg, ← sub_eq_add_neg] at hsneg
  apply hsneg.congr
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    congrArg norm (magneticImage_cross_pointwise G theta 1 h f p z).symm

/-- The actual image cell integrals sum to the original plane cross integral. -/
theorem tsum_magneticImage_cellInner_eq_planeInner (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    (∑' p : ℤ × ℤ, ∫ z, conj (h.val z) * magneticImage G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f p z ∂cellMeasure G 1) = planeInner h.val f := by
  calc
    _ = ∑' p : ℤ × ℤ, ∫ z,
        conj (h.val (z - latticePeriod G.omega1 G.omega2 p)) *
          f (z - latticePeriod G.omega1 G.omega2 p) ∂cellMeasure G 1 := by
      apply tsum_congr
      intro p
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => magneticImage_cross_pointwise G theta 1 h f p z
    _ = ∑' p : ℤ × ℤ, ∫ z,
        conj (h.val (z + latticePeriod G.omega1 G.omega2 p)) *
          f (z + latticePeriod G.omega1 G.omega2 p) ∂cellMeasure G 1 := by
      simpa only [Equiv.neg_apply, latticePeriod_neg, ← sub_eq_add_neg] using
        (Equiv.neg (ℤ × ℤ)).tsum_eq (fun p : ℤ × ℤ => ∫ z,
          conj (h.val (z + latticePeriod G.omega1 G.omega2 p)) *
            f (z + latticePeriod G.omega1 G.omega2 p) ∂cellMeasure G 1)
    _ = _ := tsum_cellIntegral_eq_planeIntegral G (fun z => conj (h.val z) * f z)
      (rawLLL_seed_cross_integrable G theta 1 h f hf)

/-- The periodized cross product itself has the correct actual cell L1 domain. -/
theorem magneticPeriodization_cross_integrable_cell (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    Integrable (fun z => conj (h.val z) * magneticPeriodization G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f z) (cellMeasure G 1) := by
  let F : (ℤ × ℤ) → ℂ → ℂ := fun p z => conj (h.val z) * magneticImage
    G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 f p z
  have hF (p : ℤ × ℤ) : Integrable (F p) (cellMeasure G 1) :=
    magneticImage_cross_integrable_cell G theta h f hf p
  have hu := rawLLL_seed_cross_integrable G theta 1 h f hf
  have hl : (∑' p : ℤ × ℤ, ∫⁻ z, ‖F p z‖ₑ ∂cellMeasure G 1) =
      ∫⁻ z, ‖conj (h.val z) * f z‖ₑ ∂planeMeasure := by
    calc
      _ = ∑' p : ℤ × ℤ, ∫⁻ z,
          ‖conj (h.val (z - latticePeriod G.omega1 G.omega2 p)) *
            f (z - latticePeriod G.omega1 G.omega2 p)‖ₑ ∂cellMeasure G 1 := by
        apply tsum_congr
        intro p
        apply lintegral_congr
        intro z
        exact congrArg enorm (magneticImage_cross_pointwise G theta 1 h f p z)
      _ = ∑' p : ℤ × ℤ, ∫⁻ z,
          ‖conj (h.val (z + latticePeriod G.omega1 G.omega2 p)) *
            f (z + latticePeriod G.omega1 G.omega2 p)‖ₑ ∂cellMeasure G 1 := by
        simpa only [Equiv.neg_apply, latticePeriod_neg, ← sub_eq_add_neg] using
          (Equiv.neg (ℤ × ℤ)).tsum_eq (fun p : ℤ × ℤ => ∫⁻ z,
            ‖conj (h.val (z + latticePeriod G.omega1 G.omega2 p)) *
              f (z + latticePeriod G.omega1 G.omega2 p)‖ₑ ∂cellMeasure G 1)
      _ = _ := tsum_cellLIntegral_eq_planeLIntegral G (fun z => ‖conj (h.val z) * f z‖ₑ)
  have htsum : Integrable (fun z => ∑' p : ℤ × ℤ, F p z) (cellMeasure G 1) := by
    refine ⟨(AEMeasurable.tsum fun p => (hF p).aemeasurable).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum (fun p => (hF p).aestronglyMeasurable.enorm), hl]
    exact hu.hasFiniteIntegral
  simpa only [F, magneticPeriodization, tsum_mul_left] using htsum

/-- Actual magnetic inner unfolding, with only the seed's plane-L1 domain
as a premise. No LLL membership of the periodized seed is assumed. -/
theorem cellInner_magneticPeriodization_eq_planeInner (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (f : ℂ → ℂ) (hf : Integrable f planeMeasure) :
    cellInner G 1 h.val (magneticPeriodization G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 f) = planeInner h.val f := by
  have hi := integral_tsum_of_summable_integral_norm
    (magneticImage_cross_integrable_cell G theta h f hf)
    (summable_magneticImage_cross_cellIntegral_norm G theta h f hf)
  calc
    _ = ∫ z, ∑' p : ℤ × ℤ, conj (h.val z) * magneticImage G.M 1 G.omega1 G.omega2
        theta.theta1 theta.theta2 f p z ∂cellMeasure G 1 := by
      simp only [cellInner, magneticPeriodization, tsum_mul_left]
    _ = ∑' p : ℤ × ℤ, ∫ z, conj (h.val z) * magneticImage G.M 1 G.omega1 G.omega2
        theta.theta1 theta.theta2 f p z ∂cellMeasure G 1 := hi.symm
    _ = _ := tsum_magneticImage_cellInner_eq_planeInner G theta h f hf

/-- L1 preservation for the existing actual planar magnetic translate. -/
theorem magneticTranslate_integrable (k : ℝ) (R : ℂ) (f : ℂ → ℂ)
    (hf : Integrable f planeMeasure) : Integrable (magneticTranslate k R f) planeMeasure := by
  have hi := (planeMeasure_translate R).integrable_comp_of_integrable hf
  apply hi.mono (magnetic_aestronglyMeasurable k R f hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => (magneticTranslate_norm k R z f).le

/-- The actual accepted translated canonical jet satisfies the L1 seed domain. -/
theorem translatedPlaneJet_integrable (j : ℕ) (R : ℂ) :
    Integrable (translatedPlaneJet j R) planeMeasure :=
  magneticTranslate_integrable 1 R (planeJet j)
    (TorusLean.Fermion.CanonicalPlaneJets.planeJet_integrable j)

/-- Domain of the actual rawJetFunction cross product in the existing μ1. -/
theorem rawJet_cross_integrable_cell (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    Integrable (fun z => conj (h.val z) * rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 j R z) (cellMeasure G 1) :=
  magneticPeriodization_cross_integrable_cell G theta h (translatedPlaneJet j R)
    (translatedPlaneJet_integrable j R)

/-- Inner unfolding instantiated at every original j and translated seed R. -/
theorem rawJet_inner_unfold (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    cellInner G 1 h.val (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 j R) = planeInner h.val (translatedPlaneJet j R) :=
  cellInner_magneticPeriodization_eq_planeInner G theta h (translatedPlaneJet j R)
    (translatedPlaneJet_integrable j R)

/-- Genuine absolute integral sum for the actual translated jet images. -/
theorem summable_rawJet_cross_cellIntegral_norm (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    Summable (fun p : ℤ × ℤ => ∫ z,
      ‖conj (h.val z) * magneticImage G.M 1 G.omega1 G.omega2
        theta.theta1 theta.theta2 (translatedPlaneJet j R) p z‖ ∂cellMeasure G 1) :=
  summable_magneticImage_cross_cellIntegral_norm G theta h (translatedPlaneJet j R)
    (translatedPlaneJet_integrable j R)

#print axioms rawLLL_norm_add_period
#print axioms rawLLL_global_norm_bound
#print axioms rawLLL_seed_cross_integrable
#print axioms magneticImage_cross_pointwise
#print axioms magneticImage_cross_integrable_cell
#print axioms summable_magneticImage_cross_cellIntegral_norm
#print axioms tsum_magneticImage_cellInner_eq_planeInner
#print axioms magneticPeriodization_cross_integrable_cell
#print axioms cellInner_magneticPeriodization_eq_planeInner
#print axioms magneticTranslate_integrable
#print axioms translatedPlaneJet_integrable
#print axioms rawJet_cross_integrable_cell
#print axioms rawJet_inner_unfold
#print axioms summable_rawJet_cross_cellIntegral_norm

end TorusLean.Shared.MagneticCellUnfolding
