import torus.shared.ThermalCoherentSpectralDoubleRegularity
import torus.shared.ThermalCoherentSpectralIntegralPositive
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual two-offset thermal spectrum on every finite polynomial core.
The ordered double series is summable by nonnegative controlled integration,
using a genuine joint L1 domain before Fubini. The single Sym2 factor 1/2
is introduced only in the final normalized form; no COM factor occurs here. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSpectralDouble
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.ThermalCoherentMoments
open TorusLean.Shared.ThermalCoherentGaussian TorusLean.Shared.ThermalCoherentDoubleGaussian
open TorusLean.Shared.ThermalCoherentDoubleRegularity TorusLean.Shared.ThermalCoherentDoubleIntegral
open TorusLean.Shared.ThermalCoherentSpectralIntegral
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open scoped BigOperators

local instance spectral_physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩
local instance : SFinite planeMeasure := by unfold planeMeasure; infer_instance

/-- Ordered raw-jet spectator pair on the original factorial core. -/
def doubleJetNormSq (G : Geometry) (theta : Twist)
    (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ) (jm : ℕ × ℕ) : ℝ :=
  occupationMetricNormSq (fun _ => 1)
    (modeAnnihilate (rawJetMode G theta jm.2 R)
      (modeAnnihilate (rawJetMode G theta jm.1 R) p))

theorem doubleJetNormSq_nonneg (G : Geometry) (theta : Twist)
    (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ) (jm : ℕ × ℕ) :
    0 ≤ doubleJetNormSq G theta R p jm := occupationMetricNormSq_nonneg _ _

private def firstSpectralIntegrand (G : Geometry) (theta : Twist) (a : ℝ)
    (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ) (j : ℕ) (beta : ℂ) : ℝ :=
  thermalEigenvalue a j * thermalWeight a beta * occupationMetricNormSq (fun _ => 1)
    (modeAnnihilate (rawJetMode G theta j R)
      (modeAnnihilate (evaluationCoordinates G theta (R+beta)) p))

private theorem firstSpectralIntegrand_nonneg (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ) (j : ℕ) (beta : ℂ) :
    0 ≤ firstSpectralIntegrand G theta a R p j beta :=
  mul_nonneg (mul_nonneg (thermalEigenvalue_pos a ha j).le (thermalWeight_pos a beta).le)
    (occupationMetricNormSq_nonneg _ _)

private theorem firstSpectralIntegrand_continuous (G : Geometry) (theta : Twist)
    (a : ℝ) (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ) (j : ℕ) :
    Continuous (firstSpectralIntegrand G theta a R p j) := by
  change Continuous (fun beta => thermalEigenvalue a j * thermalWeight a beta *
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate (rawJetMode G theta j R)
      (modeAnnihilate (evaluationCoordinates G theta (R+beta)) p)))
  exact ((thermalWeight_continuous a).const_mul (thermalEigenvalue a j)).mul
    (fixed_rawJet_spectator_normSq_continuous G theta j R p)

private theorem firstSpectralIntegrand_pointwise (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) (beta : ℂ) :
    HasSum (fun j => firstSpectralIntegrand G theta a R p j beta)
      (∫ gamma, bareDoubleThermalIntegrand G theta a R p (beta,gamma) ∂planeMeasure) := by
  have h := (actual_evaluation_occupation_hasSum G theta hG a ha R
    (modeAnnihilate (evaluationCoordinates G theta (R+beta)) p)).mul_left
      (thermalWeight a beta)
  have he : thermalWeight a beta *
      (∫ gamma, thermalWeight a gamma * occupationMetricNormSq (fun _ => 1)
        (modeAnnihilate (evaluationCoordinates G theta (R+gamma))
          (modeAnnihilate (evaluationCoordinates G theta (R+beta)) p)) ∂planeMeasure) =
      ∫ gamma, bareDoubleThermalIntegrand G theta a R p (beta,gamma) ∂planeMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun gamma => by
      simp only [bareDoubleThermalIntegrand, thermalProductWeight, spectatorPair,
        LinearMap.comp_apply, mul_assoc]
  rw [he] at h
  exact h.congr_fun fun j => by dsimp only [firstSpectralIntegrand]; ring

private theorem firstSpectralIntegrand_fiber_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) (j : ℕ) :
    HasSum (fun m => thermalEigenvalue a j * thermalEigenvalue a m *
      doubleJetNormSq G theta R p (j,m))
      (∫ beta, firstSpectralIntegrand G theta a R p j beta ∂planeMeasure) := by
  have h := (actual_evaluation_occupation_hasSum G theta hG a ha R
    (modeAnnihilate (rawJetMode G theta j R) p)).mul_left (thermalEigenvalue a j)
  have he : thermalEigenvalue a j *
      (∫ beta, thermalWeight a beta * occupationMetricNormSq (fun _ => 1)
        (modeAnnihilate (evaluationCoordinates G theta (R+beta))
          (modeAnnihilate (rawJetMode G theta j R) p)) ∂planeMeasure) =
      ∫ beta, firstSpectralIntegrand G theta a R p j beta ∂planeMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun beta => by
      dsimp only [firstSpectralIntegrand]
      rw [mode_annihilate_commute (evaluationCoordinates G theta (R+beta))
        (rawJetMode G theta j R) p]
      simp only [firstSpectralIntegrand, mul_assoc]
  rw [he] at h
  exact h.congr_fun fun m => by dsimp only [doubleJetNormSq]; ring

/-- The whole ordered double spectrum sums to the genuine joint integral.
Both summation orders are justified by positivity and joint integrability. -/
theorem bareDoubleThermal_hasSum (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    HasSum (fun jm : ℕ × ℕ => thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
      doubleJetNormSq G theta R p jm)
      (∫ x, bareDoubleThermalIntegrand G theta a R p x ∂planeMeasure.prod planeMeasure) := by
  have hG : 1 ≤ systole G := by linarith
  have hJoint := bareDoubleThermalIntegrand_integrable G theta a ha R p hL
  have houter := integral_hasSum_of_nonnegative_hasSum planeMeasure
    (firstSpectralIntegrand G theta a R p)
    (fun beta => ∫ gamma, bareDoubleThermalIntegrand G theta a R p (beta,gamma) ∂planeMeasure)
    (firstSpectralIntegrand_nonneg G theta a ha R p)
    (fun j => (firstSpectralIntegrand_continuous G theta a R p j).aestronglyMeasurable)
    (firstSpectralIntegrand_pointwise G theta hG a ha R p) hJoint.integral_prod_left
  have hfiber := firstSpectralIntegrand_fiber_hasSum G theta hG a ha R p
  let t : ℕ × ℕ → ℝ := fun jm => thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
    doubleJetNormSq G theta R p jm
  have ht : ∀ jm, 0 ≤ t jm := fun jm =>
    mul_nonneg (mul_nonneg (thermalEigenvalue_pos a ha jm.1).le
      (thermalEigenvalue_pos a ha jm.2).le) (doubleJetNormSq_nonneg G theta R p jm)
  have hs : Summable t := (summable_prod_of_nonneg ht).2 ⟨fun j => (hfiber j).summable, by
    have he : (fun j => ∑' m, t (j,m)) =
        (fun j => ∫ beta, firstSpectralIntegrand G theta a R p j beta ∂planeMeasure) :=
      funext fun j => (hfiber j).tsum_eq
    rw [he]
    exact houter.summable⟩
  have he := (hs.hasSum.prod_fiberwise hfiber).unique houter
  rw [← integral_prod _ hJoint] at he
  exact he ▸ hs.hasSum

/-- The normalized Sym2 spectrum carries exactly one external half. -/
theorem halfDoubleThermal_hasSum (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    HasSum (fun jm : ℕ × ℕ => (1/2 : ℝ) *
      (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 * doubleJetNormSq G theta R p jm))
      ((1/2 : ℝ) * ∫ x, bareDoubleThermalIntegrand G theta a R p x
        ∂planeMeasure.prod planeMeasure) :=
  (bareDoubleThermal_hasSum G theta a ha R p hL).mul_left (1/2 : ℝ)

/-- Literal matching to the existing fixed-anchor two-spectator integrand.
The original pair normalization is retained inside p = B_R(state). -/
theorem anchoredDoubleThermal_hasSum (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    HasSum (fun jm : ℕ × ℕ => (1/2 : ℝ) *
      (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
        doubleJetNormSq G theta R (modePair (evaluationCoordinates G theta R) p) jm))
      (∫ x, twoSpectatorIntegrand G theta a p (R,x) ∂planeMeasure.prod planeMeasure) := by
  have h := halfDoubleThermal_hasSum G theta a ha R
    (modePair (evaluationCoordinates G theta R) p) hL
  have he : (1/2 : ℝ) *
      (∫ x, bareDoubleThermalIntegrand G theta a R
        (modePair (evaluationCoordinates G theta R) p) x ∂planeMeasure.prod planeMeasure) =
      ∫ x, twoSpectatorIntegrand G theta a p (R,x) ∂planeMeasure.prod planeMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [bareDoubleThermalIntegrand, twoSpectatorIntegrand, twoSpectatorNormSq]
      ring
  rwa [he] at h

end TorusLean.Shared.ThermalCoherentSpectralDouble
