import torus.shared.PlaneJetMembership
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Actual all-j canonical plane and cell derivative reproduction

The original raw section itself supplies its canonical entire factor by
division by the original nonzero charge-one Gaussian. The factor agrees
with every original Gaussian-holomorphic witness, so no witness is supplied
to the final plane/cell formulas. The actual global bound on a raw section
and the canonical j-seed L1 theorem derive the weighted Gaussian domains,
also after the actual back-translation. No plane-L2 premise is made.

With the physical conjugate-first convention, pairing the original T_R e_j
against h gives the j-th derivative at zero of the stripped factor of
T_{-R}h, divided by the unchanged sqrt(j!). Original magnetic cell unfolding
gives the identical actual cell formula. After original all-j periodizer
membership is consumed, this functional is linear and continuous on the
actual cell-Hilbert carrier, and its actual Riesz kernel is the original
raw jet. The exact derivative-form Gram/norm identities below make no
uniform numerical budget or fermionic derivative-contact assertion.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared.PlaneJetReproducing

open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Shared.MagneticCellUnfolding
open TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetMembership
open scoped ComplexConjugate ENNReal

private theorem conjugate_integrable (f : ℂ → ℂ) {μ : Measure ℂ}
    (hf : Integrable f μ) : Integrable (fun z => conj (f z)) μ :=
  hf.congr' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => (Complex.norm_conj (f z)).symm)

private theorem gaussianFactor_conj (k : ℝ) (z : ℂ) :
    conj (gaussianFactor k z) = gaussianFactor k z := by
  rw [gaussianFactor_eq_norm, ← Complex.exp_conj, Complex.conj_ofReal]

private theorem gaussianFactor_one_square (z : ℂ) :
    gaussianFactor 1 z * gaussianFactor 1 z = Complex.exp (-(‖z‖ ^ 2 : ℂ)) := by
  simp only [gaussianFactor_eq_norm]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Canonical stripping of the actual raw charge-one section. This is an
actual function defined from h, without a selected entire witness. -/
def canonicalRawStripped (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) : ℂ → ℂ :=
  fun z => h.val z / gaussianFactor 1 z

/-- Canonical stripping agrees with every actual original factor witness.
This characterization is used to derive entire differentiability. -/
theorem canonicalRawStripped_eq_factor (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (F : ℂ → ℂ)
    (hfactor : ∀ z, h.val z = gaussianFactor 1 z * F z) :
    canonicalRawStripped G theta h = F := by
  funext z
  unfold canonicalRawStripped
  rw [hfactor]
  field_simp [gaussianFactor_ne_zero] <;> ring

/-- The canonical factor is entire, derived from the original raw-section
predicate rather than imposed as a new analytic hypothesis. -/
theorem canonicalRawStripped_differentiable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) : Differentiable ℂ (canonicalRawStripped G theta h) := by
  obtain ⟨F, hF, hfactor⟩ := h.property.1
  have hf : ∀ z, h.val z = gaussianFactor 1 z * F z := by
    simpa only [Nat.cast_one] using hfactor
  rw [canonicalRawStripped_eq_factor G theta h F hf]
  exact hF

/-- The original section has its canonical Gaussian factorization. -/
theorem canonicalRawStripped_factor (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (z : ℂ) :
    h.val z = gaussianFactor 1 z * canonicalRawStripped G theta h z := by
  unfold canonicalRawStripped
  field_simp [gaussianFactor_ne_zero] <;> ring

/-- Exact normalized original j-cross integrand after Gaussian stripping.
The conjugate acts on the canonical monomial in the physical first slot. -/
theorem planeJet_cross_factor (j : ℕ) (g F : ℂ → ℂ)
    (hfactor : ∀ z, g z = gaussianFactor 1 z * F z) (z : ℂ) :
    conj (planeJet j z) * g z =
      (Complex.exp (-(‖z‖ ^ 2 : ℂ)) * conj z ^ j * F z) /
        (Real.sqrt (j.factorial : ℝ) : ℂ) := by
  simp only [planeJet, map_div₀, map_mul, map_pow,
    gaussianFactor_conj, Complex.conj_ofReal]
  rw [hfactor]
  calc
    _ = (gaussianFactor 1 z * gaussianFactor 1 z) * conj z ^ j * F z /
        (Real.sqrt (j.factorial : ℝ) : ℂ) := by ring
    _ = _ := by rw [gaussianFactor_one_square]

/-- Actual all-j plane cross-integrability from the original raw global
bound and the original translated canonical seed L1 theorem. -/
theorem rawLLL_planeJet_plane_cross_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    Integrable (fun z => conj (translatedPlaneJet j R z) * h.val z) planeMeasure := by
  obtain ⟨C, _hC, hbound⟩ := rawLLL_global_norm_bound G theta 1 h
  apply (conjugate_integrable (translatedPlaneJet j R)
    (translatedPlaneJet_integrable j R)).mul_bdd (c := C)
      (rawLLL_continuous G theta 1 h).aestronglyMeasurable
  exact Filter.Eventually.of_forall hbound

/-- The accepted all-j Gaussian theorem's exact volume-domain is derived
from the actual raw section and the canonical j-seed L1 domain. -/
theorem rawLLL_canonical_gaussian_weighted_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) :
    Integrable (fun z => Complex.exp (-(‖z‖ ^ 2 : ℂ)) * conj z ^ j *
      canonicalRawStripped G theta h z) (volume : Measure ℂ) := by
  have hi : Integrable (fun z => conj (planeJet j z) * h.val z) planeMeasure := by
    simpa only [translatedPlaneJet, magneticTranslate_zero] using
      rawLLL_planeJet_plane_cross_integrable G theta h j 0
  have hscale : (Real.sqrt (j.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (planeJet_scale_pos j))
  have hw : Integrable (fun z => Complex.exp (-(‖z‖ ^ 2 : ℂ)) * conj z ^ j *
      canonicalRawStripped G theta h z) planeMeasure :=
    (hi.mul_const (Real.sqrt (j.factorial : ℝ) : ℂ)).congr
    (Filter.Eventually.of_forall fun z => by
      exact (congrArg (fun w : ℂ => w * (Real.sqrt (j.factorial : ℝ) : ℂ))
        (planeJet_cross_factor j h.val (canonicalRawStripped G theta h)
          (canonicalRawStripped_factor G theta h) z)).trans
        (div_mul_cancel₀ _ hscale))
  rw [planeMeasure] at hw
  exact (integrable_smul_measure planeMeasure_scale_pos.ne' ENNReal.ofReal_ne_top).mp hw

/-- Actual plane cross domain after T_{-R}h, derived from the same actual
global raw norm bound. No plane-L2 domain is imposed or inferred. -/
theorem backTranslate_planeJet_cross_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    Integrable (fun z => conj (planeJet j z) * magneticTranslate 1 (-R) h.val z)
      planeMeasure := by
  obtain ⟨C, _hC, hbound⟩ := rawLLL_global_norm_bound G theta 1 h
  apply (conjugate_integrable (planeJet j) (planeJet_integrable j)).mul_bdd (c := C)
    (magnetic_aestronglyMeasurable 1 (-R) h.val
      (rawLLL_continuous G theta 1 h).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    rw [magneticTranslate_norm]
    exact hbound (z - -R)

/-- The actual back-translated canonical entire factor satisfies the
accepted Gaussian weighted volume-domain for every actual j. -/
theorem backTranslate_canonical_gaussian_weighted_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    Integrable (fun z => Complex.exp (-(‖z‖ ^ 2 : ℂ)) * conj z ^ j *
      translatedStrippedFactor (-R) (canonicalRawStripped G theta h) z)
      (volume : Measure ℂ) := by
  have hi := backTranslate_planeJet_cross_integrable G theta h j R
  have hscale : (Real.sqrt (j.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (planeJet_scale_pos j))
  have hw : Integrable (fun z => Complex.exp (-(‖z‖ ^ 2 : ℂ)) * conj z ^ j *
      translatedStrippedFactor (-R) (canonicalRawStripped G theta h) z) planeMeasure :=
    (hi.mul_const (Real.sqrt (j.factorial : ℝ) : ℂ)).congr
    (Filter.Eventually.of_forall fun z => by
      exact (congrArg (fun w : ℂ => w * (Real.sqrt (j.factorial : ℝ) : ℂ))
        (planeJet_cross_factor j (magneticTranslate 1 (-R) h.val)
          (translatedStrippedFactor (-R) (canonicalRawStripped G theta h))
          (magneticTranslate_stripped_factor (-R) h.val (canonicalRawStripped G theta h)
            (canonicalRawStripped_factor G theta h)) z)).trans
        (div_mul_cancel₀ _ hscale))
  rw [planeMeasure] at hw
  exact (integrable_smul_measure planeMeasure_scale_pos.ne' ENNReal.ofReal_ne_top).mp hw

private theorem normalized_plane_reproduces_factor (j : ℕ) (g F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hfactor : ∀ z, g z = gaussianFactor 1 z * F z)
    (hweight : Integrable (fun z => Complex.exp (-(‖z‖ ^ 2 : ℂ)) * conj z ^ j * F z)
      (volume : Measure ℂ)) :
    planeInner (planeJet j) g =
      iteratedDeriv j F 0 / (Real.sqrt (j.factorial : ℝ) : ℂ) := by
  have hr := TorusLean.Fermion.PlaneGaussianReproducing.gaussian_reproducing_derivative
    j F hF hweight
  calc
    _ = (ENNReal.ofReal (1 / Real.pi)).toReal •
        (((Real.pi : ℂ) * iteratedDeriv j F 0) /
          (Real.sqrt (j.factorial : ℝ) : ℂ)) := by
      unfold planeInner
      simp_rw [planeJet_cross_factor j g F hfactor]
      rw [planeMeasure, integral_smul_measure, integral_div, hr]
    _ = _ := by
      rw [ENNReal.toReal_ofReal (one_div_pos.mpr Real.pi_pos).le, Complex.real_smul]
      have hp : ((1 / Real.pi : ℝ) : ℂ) * (Real.pi : ℂ) = 1 := by
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
      calc
        _ = ((((1 / Real.pi : ℝ) : ℂ) * (Real.pi : ℂ)) * iteratedDeriv j F 0) /
            (Real.sqrt (j.factorial : ℝ) : ℂ) := by ring
        _ = _ := by rw [hp, one_mul]

/-- Original all-j plane reproduction at the origin, stated solely for
the actual raw section and its canonical stripped function. -/
theorem rawLLL_planeJet_plane_reproduces_origin (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) :
    planeInner (planeJet j) h.val =
      iteratedDeriv j (canonicalRawStripped G theta h) 0 /
        (Real.sqrt (j.factorial : ℝ) : ℂ) :=
  normalized_plane_reproduces_factor j h.val (canonicalRawStripped G theta h)
    (canonicalRawStripped_differentiable G theta h) (canonicalRawStripped_factor G theta h)
    (rawLLL_canonical_gaussian_weighted_integrable G theta h j)

/-- Actual normalized canonical derivative coefficient, with the entire
factor of the original back-translation and unchanged sqrt(j!) scale. -/
def rawJetCoefficient (G : Geometry) (theta : Twist) (h : RawLLL G theta 1)
    (j : ℕ) (R : ℂ) : ℂ :=
  iteratedDeriv j (translatedStrippedFactor (-R) (canonicalRawStripped G theta h)) 0 /
    (Real.sqrt (j.factorial : ℝ) : ℂ)

/-- Original translated all-j plane reproduction with the physical
conjugate-first orientation. All analytic domains are derived from h. -/
theorem rawLLL_translatedPlaneJet_plane_reproduces (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    planeInner (translatedPlaneJet j R) h.val = rawJetCoefficient G theta h j R := by
  have hrep := normalized_plane_reproduces_factor j (magneticTranslate 1 (-R) h.val)
    (translatedStrippedFactor (-R) (canonicalRawStripped G theta h))
    (translatedStrippedFactor_differentiable (-R) _
      (canonicalRawStripped_differentiable G theta h))
    (magneticTranslate_stripped_factor (-R) h.val (canonicalRawStripped G theta h)
      (canonicalRawStripped_factor G theta h))
    (backTranslate_canonical_gaussian_weighted_integrable G theta h j R)
  calc
    _ = planeInner (planeJet j) (magneticTranslate 1 (-R) h.val) := by
      simpa only [translatedPlaneJet, magneticTranslate_inverse] using
        planeInner_translate 1 R (planeJet j) (magneticTranslate 1 (-R) h.val)
    _ = rawJetCoefficient G theta h j R := hrep

/-- Compatibility at j=0 with actual point evaluation, rather than a
different normalization or an inferred higher-jet Gram identity. -/
theorem rawJetCoefficient_zero (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R : ℂ) : rawJetCoefficient G theta h 0 R = h.val R :=
  (rawLLL_translatedPlaneJet_plane_reproduces G theta h 0 R).symm.trans
    (rawLLL_translatedGround_plane_reproduces G theta h R)

/-- Reversed plane slots retain the actual complex conjugate. -/
theorem rawLLL_translatedPlaneJet_plane_reproduces_reversed (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    planeInner h.val (translatedPlaneJet j R) = conj (rawJetCoefficient G theta h j R) := by
  rw [← planeInner_conj_symm (translatedPlaneJet j R) h.val,
    rawLLL_translatedPlaneJet_plane_reproduces]

/-- Actual first-slot raw periodizer cell domain, independently derived
by the accepted unfolding theorem and conjugate symmetry. -/
theorem rawPlaneJet_cell_cross_integrable (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    Integrable (fun z => conj (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 j R z) * h.val z) (cellMeasure G 1) := by
  have hi := conjugate_integrable _ (rawJet_cross_integrable_cell G theta h j R)
  simpa only [map_mul, Complex.conj_conj, mul_comm] using hi

/-- Actual reversed cell reproduction obtained from original magnetic
cell unfolding, with its conjugate-first convention preserved. -/
theorem rawPlaneJet_cell_reproduces_reversed (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    cellInner G 1 h.val (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 j R) = conj (rawJetCoefficient G theta h j R) :=
  (rawJet_inner_unfold G theta h j R).trans
    (rawLLL_translatedPlaneJet_plane_reproduces_reversed G theta h j R)

/-- Actual unrescaled all-j cell derivative reproduction. The final
formula takes only the actual raw section, jet index and centre. -/
theorem rawPlaneJet_cell_reproduces (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    cellInner G 1 (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 j R) h.val = rawJetCoefficient G theta h j R := by
  rw [← cellInner_conj_symm G 1 h.val (rawJetFunction G.M G.omega1 G.omega2
    theta.theta1 theta.theta2 j R), rawPlaneJet_cell_reproduces_reversed,
    Complex.conj_conj]

/-- This Hilbert-carrier form consumes the independently proved original
all-j periodizer membership. The carrier and inner product are physical. -/
theorem rawPlaneJet_inner_reproduces (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (j : ℕ) (R : ℂ) :
    inner ℂ (rawPlaneJet G theta j R) h = rawJetCoefficient G theta h j R := by
  rw [lll_inner_eq_cellInner]
  exact rawPlaneJet_cell_reproduces G theta h j R

/-- The actual normalized derivative functional is linear, proved from
its original cell representation. Its toFun is the canonical derivative
formula, not a coordinate or supplied kernel functional. -/
def canonicalJetEvaluationLinear (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    LLL G theta 1 →ₗ[ℂ] ℂ where
  toFun h := rawJetCoefficient G theta h j R
  map_add' f g := by
    rw [← rawPlaneJet_inner_reproduces G theta (f + g) j R,
      ← rawPlaneJet_inner_reproduces G theta f j R,
      ← rawPlaneJet_inner_reproduces G theta g j R]
    exact inner_add_right _ _ _
  map_smul' c f := by
    change rawJetCoefficient G theta (c • f) j R = c * rawJetCoefficient G theta f j R
    rw [← rawPlaneJet_inner_reproduces G theta (c • f) j R,
      ← rawPlaneJet_inner_reproduces G theta f j R]
    exact inner_smul_right _ _ _

/-- Continuity of the actual derivative functional follows from the
already derived finite physical LLL dimension. No budget is supplied. -/
def canonicalJetEvaluation (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    LLL G theta 1 →L[ℂ] ℂ :=
  (canonicalJetEvaluationLinear G theta j R).toContinuousLinearMap

theorem canonicalJetEvaluation_apply (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (h : LLL G theta 1) :
    canonicalJetEvaluation G theta j R h = rawJetCoefficient G theta h j R := rfl

/-- Riesz kernel for the actual canonical derivative functional on the
existing physical charge-one cell-Hilbert space. -/
def canonicalJetEvaluationKernel (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    LLL G theta 1 :=
  (InnerProductSpace.toDual ℂ (LLL G theta 1)).symm (canonicalJetEvaluation G theta j R)

theorem canonicalJetEvaluationKernel_reproduces (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (h : LLL G theta 1) :
    inner ℂ (canonicalJetEvaluationKernel G theta j R) h = rawJetCoefficient G theta h j R :=
  InnerProductSpace.toDual_symm_apply

/-- Actual all-j original periodizer equals the actual canonical
derivative Riesz kernel, after consuming original all-j membership. -/
theorem rawPlaneJet_eq_canonicalJetEvaluationKernel (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) : rawPlaneJet G theta j R = canonicalJetEvaluationKernel G theta j R := by
  apply ext_inner_right ℂ
  intro h
  exact (rawPlaneJet_inner_reproduces G theta h j R).trans
    (canonicalJetEvaluationKernel_reproduces G theta j R h).symm

/-- Exact norm identity with the derived actual derivative-evaluation
operator norm. No uniform numerical bound is inferred. -/
theorem canonicalJetEvaluationKernel_norm (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) :
    ‖canonicalJetEvaluationKernel G theta j R‖ = ‖canonicalJetEvaluation G theta j R‖ :=
  (InnerProductSpace.toDual ℂ (LLL G theta 1)).symm.norm_map _

/-- Exact actual all-j cell Gram in canonical derivative form. It uses
both original raw-jet memberships; it is not a double-lattice expansion
or a uniform Gram-error estimate. -/
theorem rawPlaneJet_cell_gram (G : Geometry) (theta : Twist)
    (j m : ℕ) (R S : ℂ) :
    cellInner G 1
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R)
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 m S) =
      rawJetCoefficient G theta (rawPlaneJet G theta m S) j R :=
  rawPlaneJet_cell_reproduces G theta (rawPlaneJet G theta m S) j R

/-- Original cell norm squared equals the real self derivative
coefficient. This asserts neither nonvanishing nor a quantitative budget. -/
theorem rawPlaneJet_cell_norm_sq (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    (∫ z, ‖rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R z‖ ^ 2
      ∂cellMeasure G 1) = (rawJetCoefficient G theta (rawPlaneJet G theta j R) j R).re := by
  have h := congrArg Complex.re (rawPlaneJet_cell_gram G theta j j R R)
  rw [cellInner_self, Complex.ofReal_re] at h
  exact h

#print axioms canonicalRawStripped
#print axioms canonicalRawStripped_eq_factor
#print axioms canonicalRawStripped_differentiable
#print axioms canonicalRawStripped_factor
#print axioms planeJet_cross_factor
#print axioms rawLLL_planeJet_plane_cross_integrable
#print axioms rawLLL_canonical_gaussian_weighted_integrable
#print axioms backTranslate_planeJet_cross_integrable
#print axioms backTranslate_canonical_gaussian_weighted_integrable
#print axioms rawLLL_planeJet_plane_reproduces_origin
#print axioms rawJetCoefficient
#print axioms rawLLL_translatedPlaneJet_plane_reproduces
#print axioms rawJetCoefficient_zero
#print axioms rawLLL_translatedPlaneJet_plane_reproduces_reversed
#print axioms rawPlaneJet_cell_cross_integrable
#print axioms rawPlaneJet_cell_reproduces_reversed
#print axioms rawPlaneJet_cell_reproduces
#print axioms rawPlaneJet_inner_reproduces
#print axioms canonicalJetEvaluationLinear
#print axioms canonicalJetEvaluation
#print axioms canonicalJetEvaluation_apply
#print axioms canonicalJetEvaluationKernel
#print axioms canonicalJetEvaluationKernel_reproduces
#print axioms rawPlaneJet_eq_canonicalJetEvaluationKernel
#print axioms canonicalJetEvaluationKernel_norm
#print axioms rawPlaneJet_cell_gram
#print axioms rawPlaneJet_cell_norm_sq

end TorusLean.Shared.PlaneJetReproducing
