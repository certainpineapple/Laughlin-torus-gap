import torus.shared.MagneticCellUnfolding
import PlaneGaussianReproducing

/-!
# Actual ground-jet evaluation against physical raw sections

The actual globally bounded raw section supplies the Gaussian-weighted L1
domain of the accepted plane reproducing theorem. The translated formula
uses the explicit entire factor of the actual magnetic translate by -R and
the existing plane change of variables, without a plane-L2 assumption.

The physical convention is conjugate linear in the first slot:
`planeInner (translatedPlaneJet 0 R) h = h R`, whereas the reversed slots
give `conj (h R)`. Combining this with actual magnetic cell unfolding yields
`cellInner G 1 (rawJetFunction ... 0 R) h = h R` on every actual raw section.
No assertion of raw membership or Riesz-kernel identification of the
periodized ground jet is made here.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared.GroundJetReproducing

open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Shared.MagneticCellUnfolding
open scoped ComplexConjugate ENNReal

private theorem conjugate_integrable (f : ℂ → ℂ) {μ : Measure ℂ}
    (hf : Integrable f μ) : Integrable (fun z => conj (f z)) μ :=
  hf.congr' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => (Complex.norm_conj (f z)).symm)

private theorem gaussianFactor_conj (k : ℝ) (z : ℂ) :
    conj (gaussianFactor k z) = gaussianFactor k z := by
  rw [gaussianFactor_eq_norm, ← Complex.exp_conj, Complex.conj_ofReal]

/-- The original j=0 seed is the original charge-one Gaussian. -/
theorem planeJet_zero_eq_gaussianFactor (z : ℂ) : planeJet 0 z = gaussianFactor 1 z := by
  simp [planeJet]

/-- The actual ground cross integrand strips to the exact Gaussian weight. -/
theorem groundJet_cross_factor (g F : ℂ → ℂ)
    (hfactor : ∀ z, g z = gaussianFactor 1 z * F z) (z : ℂ) :
    conj (planeJet 0 z) * g z = Complex.exp (-(‖z‖^2 : ℂ)) * F z := by
  rw [planeJet_zero_eq_gaussianFactor, hfactor, gaussianFactor_conj, ← mul_assoc]
  congr 1
  simp only [gaussianFactor_eq_norm]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every actual raw section can be paired with the actual translated ground
seed on the plane, with its domain derived from the actual global norm bound. -/
theorem rawLLL_ground_plane_cross_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) :
    Integrable (fun z => conj (translatedPlaneJet 0 R z) * h.val z) planeMeasure := by
  obtain ⟨C, _hC, hbound⟩ := rawLLL_global_norm_bound G theta 1 h
  apply (conjugate_integrable (translatedPlaneJet 0 R)
    (translatedPlaneJet_integrable 0 R)).mul_bdd (c := C)
      (rawLLL_continuous G theta 1 h).aestronglyMeasurable
  exact Filter.Eventually.of_forall hbound

/-- The accepted Gaussian theorem's volume-domain hypothesis is derived from
the actual raw section and its original Gaussian-holomorphic witness. -/
theorem rawLLL_gaussian_weighted_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (F : ℂ → ℂ)
    (hfactor : ∀ z, h.val z = gaussianFactor 1 z * F z) :
    Integrable (fun z => Complex.exp (-(‖z‖^2 : ℂ)) * F z) (volume : Measure ℂ) := by
  have hi : Integrable (fun z => conj (planeJet 0 z) * h.val z) planeMeasure := by
    simpa only [translatedPlaneJet, magneticTranslate_zero] using
      rawLLL_ground_plane_cross_integrable G theta h 0
  have hw := hi.congr (Filter.Eventually.of_forall fun z => groundJet_cross_factor h.val F hfactor z)
  rw [planeMeasure] at hw
  exact (integrable_smul_measure planeMeasure_scale_pos.ne' ENNReal.ofReal_ne_top).mp hw

/-- The explicit entire factor of the actual charge-one magnetic translate. -/
def translatedStrippedFactor (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (z * conj x - (x * conj x) / 2) * F (z - x)

theorem translatedStrippedFactor_differentiable (x : ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) : Differentiable ℂ (translatedStrippedFactor x F) := by
  exact (((differentiable_id.mul_const (conj x)).sub_const
    ((x * conj x) / 2)).cexp).mul (hF.comp (differentiable_id.sub_const x))

/-- Exact Gaussian stripping of the actual magnetic translate, with its
phase and displacement retained in the explicit entire factor. -/
theorem magneticTranslate_stripped_factor (x : ℂ) (g F : ℂ → ℂ)
    (hfactor : ∀ z, g z = gaussianFactor 1 z * F z) (z : ℂ) :
    magneticTranslate 1 x g z = gaussianFactor 1 z * translatedStrippedFactor x F z := by
  unfold translatedStrippedFactor
  rw [magneticTranslate, hfactor, gaussianFactor, gaussianFactor, ← mul_assoc,
    ← Complex.exp_add]
  rw [gaussian_translate_exponents, Complex.exp_add]
  simp only [Complex.ofReal_one, one_mul]
  ring

/-- Pairing the actual back-translated raw section with the actual plane
ground seed is integrable; no global L2 domain is supplied or inferred. -/
theorem backTranslate_ground_cross_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) :
    Integrable (fun z => conj (planeJet 0 z) * magneticTranslate 1 (-R) h.val z) planeMeasure := by
  obtain ⟨C, _hC, hbound⟩ := rawLLL_global_norm_bound G theta 1 h
  apply (conjugate_integrable (planeJet 0) (planeJet_integrable 0)).mul_bdd (c := C)
    (magnetic_aestronglyMeasurable 1 (-R) h.val
      (rawLLL_continuous G theta 1 h).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    rw [magneticTranslate_norm]
    exact hbound (z - -R)

/-- Gaussian-weighted volume integrability for the explicit entire factor
of T_{-R}h, derived from the actual bounded section and canonical seed L1. -/
theorem backTranslate_gaussian_weighted_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) (F : ℂ → ℂ)
    (hfactor : ∀ z, h.val z = gaussianFactor 1 z * F z) :
    Integrable (fun z => Complex.exp (-(‖z‖^2 : ℂ)) *
      translatedStrippedFactor (-R) F z) (volume : Measure ℂ) := by
  have hi := backTranslate_ground_cross_integrable G theta h R
  have hw := hi.congr (Filter.Eventually.of_forall fun z =>
    groundJet_cross_factor (magneticTranslate 1 (-R) h.val)
      (translatedStrippedFactor (-R) F) (magneticTranslate_stripped_factor (-R) h.val F hfactor) z)
  rw [planeMeasure] at hw
  exact (integrable_smul_measure planeMeasure_scale_pos.ne' ENNReal.ofReal_ne_top).mp hw

private theorem ground_plane_reproduces_factor (g F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hfactor : ∀ z, g z = gaussianFactor 1 z * F z)
    (hweight : Integrable (fun z => Complex.exp (-(‖z‖^2 : ℂ)) * F z) (volume : Measure ℂ)) :
    planeInner (planeJet 0) g = g 0 := by
  have hr : (∫ z : ℂ, Complex.exp (-(‖z‖^2 : ℂ)) * F z) = (Real.pi : ℂ) * F 0 := by
    simpa only [pow_zero, mul_one, iteratedDeriv_zero] using
      TorusLean.Fermion.PlaneGaussianReproducing.gaussian_reproducing_derivative 0 F hF
        (by simpa only [pow_zero, mul_one] using hweight)
  calc
    _ = (ENNReal.ofReal (1 / Real.pi)).toReal • ((Real.pi : ℂ) * F 0) := by
      unfold planeInner
      simp_rw [groundJet_cross_factor g F hfactor]
      rw [planeMeasure, integral_smul_measure, hr]
    _ = F 0 := by
      rw [ENNReal.toReal_ofReal (one_div_pos.mpr Real.pi_pos).le, Complex.real_smul]
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = g 0 := by simpa [gaussianFactor] using (hfactor 0).symm

/-- Actual j=0 plane reproduction at the origin, for every actual raw section. -/
theorem rawLLL_ground_plane_reproduces_origin (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) : planeInner (planeJet 0) h.val = h.val 0 := by
  obtain ⟨F, hF, hfactor⟩ := h.property.1
  have hf : ∀ z, h.val z = gaussianFactor 1 z * F z := by
    simpa only [Nat.cast_one] using hfactor
  exact ground_plane_reproduces_factor h.val F hF hf
    (rawLLL_gaussian_weighted_integrable G theta h F hf)

/-- Actual ground-seed reproduction at every physical point. The proof uses
T_{-R}h and the actual plane translation, without a plane L2 assumption. -/
theorem rawLLL_translatedGround_plane_reproduces (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) :
    planeInner (translatedPlaneJet 0 R) h.val = h.val R := by
  obtain ⟨F, hF, hfactor⟩ := h.property.1
  have hf : ∀ z, h.val z = gaussianFactor 1 z * F z := by
    simpa only [Nat.cast_one] using hfactor
  have hrep := ground_plane_reproduces_factor (magneticTranslate 1 (-R) h.val)
    (translatedStrippedFactor (-R) F) (translatedStrippedFactor_differentiable (-R) F hF)
    (magneticTranslate_stripped_factor (-R) h.val F hf)
    (backTranslate_gaussian_weighted_integrable G theta h R F hf)
  calc
    _ = planeInner (planeJet 0) (magneticTranslate 1 (-R) h.val) := by
      simpa only [translatedPlaneJet, magneticTranslate_inverse] using
        planeInner_translate 1 R (planeJet 0) (magneticTranslate 1 (-R) h.val)
    _ = magneticTranslate 1 (-R) h.val 0 := hrep
    _ = h.val R := by simp [magneticTranslate, magneticExponent]

/-- Actual complex conjugate symmetry of the existing plane integral. -/
theorem planeInner_conj_symm (f g : ℂ → ℂ) : conj (planeInner f g) = planeInner g f := by
  rw [planeInner, ← integral_conj]
  simp only [map_mul, Complex.conj_conj, planeInner, mul_comm]

/-- The reverse plane orientation retains the required complex conjugate. -/
theorem rawLLL_translatedGround_plane_reproduces_reversed (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) :
    planeInner h.val (translatedPlaneJet 0 R) = conj (h.val R) := by
  rw [← planeInner_conj_symm (translatedPlaneJet 0 R) h.val,
    rawLLL_translatedGround_plane_reproduces G theta h R]

/-- The concrete first-slot periodized ground-jet cell functional has its
actual L1 domain, derived from accepted magnetic cell unfolding. -/
theorem rawGroundJet_cell_cross_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) :
    Integrable (fun z => conj (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 0 R z) * h.val z) (cellMeasure G 1) := by
  have hi := conjugate_integrable _ (rawJet_cross_integrable_cell G theta h 0 R)
  simpa only [map_mul, Complex.conj_conj, mul_comm] using hi

/-- The reverse cell orientation equals conjugated point evaluation. -/
theorem rawGroundJet_cell_reproduces_reversed (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) :
    cellInner G 1 h.val (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 0 R) = conj (h.val R) :=
  (rawJet_inner_unfold G theta h 0 R).trans
    (rawLLL_translatedGround_plane_reproduces_reversed G theta h R)

/-- Concrete actual μ1 evaluation functional, before any membership or
identification of the periodized ground jet with a Riesz kernel. -/
theorem rawGroundJet_cell_reproduces (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) :
    cellInner G 1 (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 0 R) h.val = h.val R := by
  rw [← cellInner_conj_symm G 1 h.val (rawJetFunction G.M G.omega1 G.omega2
    theta.theta1 theta.theta2 0 R), rawGroundJet_cell_reproduces_reversed G theta h R,
    Complex.conj_conj]

#print axioms planeJet_zero_eq_gaussianFactor
#print axioms groundJet_cross_factor
#print axioms rawLLL_ground_plane_cross_integrable
#print axioms rawLLL_gaussian_weighted_integrable
#print axioms translatedStrippedFactor_differentiable
#print axioms magneticTranslate_stripped_factor
#print axioms backTranslate_ground_cross_integrable
#print axioms backTranslate_gaussian_weighted_integrable
#print axioms rawLLL_ground_plane_reproduces_origin
#print axioms rawLLL_translatedGround_plane_reproduces
#print axioms planeInner_conj_symm
#print axioms rawLLL_translatedGround_plane_reproduces_reversed
#print axioms rawGroundJet_cell_cross_integrable
#print axioms rawGroundJet_cell_reproduces_reversed
#print axioms rawGroundJet_cell_reproduces

end TorusLean.Shared.GroundJetReproducing
