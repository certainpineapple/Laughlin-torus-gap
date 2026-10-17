import torus.shared.ThermalCoherentSpectralOccupationAlgebra
import torus.shared.CoherentThermalKernel
import torus.shared.ThermalCoherentOccupation

/-! The genuine full-LLL thermal kernel yields the spectral occupation
identity on every finite polynomial core. All scalar domain and kernel
premises of the finite-basis composition lemma are discharged here using
the original raw torus jets. No new particle-number or operator premise is
introduced. The remaining anchor integration and Omega identity are separate. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSpectralOccupation
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.ThermalCoherentGaussian TorusLean.Shared.ThermalCoherentMoments
open TorusLean.Shared.CoherentThermalKernel TorusLean.Shared.ThermalCoherentOccupation
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open scoped ComplexConjugate

/-- Coordinates in the original full physical cell orthonormal basis. The
raw jets are not normalized or replaced by an orthogonal torus jet family. -/
def rawJetMode (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    Orbital (OrbitalIndex G theta) :=
  (orbitalBasis G theta).repr (rawPlaneJet G theta j R)

private theorem actual_coordinate_cross_integrable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ) (i k : OrbitalIndex G theta) :
    Integrable (fun beta => (thermalWeight a beta : ℂ) *
      conj (rawJetMode G theta 0 (R+beta) k) * rawJetMode G theta 0 (R+beta) i)
      planeMeasure := by
  simpa only [rawJetMode, OrthonormalBasis.repr_apply_apply] using
    actual_coherent_cross_integrable G theta hG a ha
      (orbitalBasis G theta k) (orbitalBasis G theta i) R

private theorem actual_coordinate_cross_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ) (i k : OrbitalIndex G theta) :
    HasSum (fun j => (thermalEigenvalue a j : ℂ) *
      conj (rawJetMode G theta j R k) * rawJetMode G theta j R i)
      (∫ beta, (thermalWeight a beta : ℂ) *
        conj (rawJetMode G theta 0 (R+beta) k) * rawJetMode G theta 0 (R+beta) i
        ∂planeMeasure) := by
  simpa only [rawJetMode, OrthonormalBasis.repr_apply_apply] using
    actual_coherent_thermal_hasSum G theta hG a ha
      (orbitalBasis G theta k) (orbitalBasis G theta i) R

/-- Real integrability for every finite core; derived from the honest
physical cross-kernel domains and a finite basis expansion. -/
theorem actual_rawJet_occupation_integrable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun beta => thermalWeight a beta * occupationMetricNormSq (fun _ => 1)
      (modeAnnihilate (rawJetMode G theta 0 (R+beta)) p)) planeMeasure :=
  weighted_modeAnnihilate_normSq_integrable planeMeasure (thermalWeight a)
    (fun beta => rawJetMode G theta 0 (R+beta))
    (actual_coordinate_cross_integrable G theta hG a ha R) p

/-- The actual full-plane coherent occupation integral has exactly the raw
jet thermal spectrum. The core is arbitrary; no sector or N bound is needed. -/
theorem actual_rawJet_occupation_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) :
    HasSum (fun j => thermalEigenvalue a j * occupationMetricNormSq (fun _ => 1)
      (modeAnnihilate (rawJetMode G theta j R) p))
      (∫ beta, thermalWeight a beta * occupationMetricNormSq (fun _ => 1)
        (modeAnnihilate (rawJetMode G theta 0 (R+beta)) p) ∂planeMeasure) :=
  weighted_modeAnnihilate_normSq_hasSum planeMeasure (thermalWeight a)
    (fun beta => rawJetMode G theta 0 (R+beta)) (fun j => rawJetMode G theta j R)
    (thermalEigenvalue a) (actual_coordinate_cross_integrable G theta hG a ha R)
    (actual_coordinate_cross_hasSum G theta hG a ha R) p

theorem actual_rawJet_occupation_integral (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) :
    (∫ beta, thermalWeight a beta * occupationMetricNormSq (fun _ => 1)
      (modeAnnihilate (rawJetMode G theta 0 (R+beta)) p) ∂planeMeasure) =
        ∑' j, thermalEigenvalue a j * occupationMetricNormSq (fun _ => 1)
          (modeAnnihilate (rawJetMode G theta j R) p) :=
  (actual_rawJet_occupation_hasSum G theta hG a ha R p).tsum_eq.symm

/-- Compatibility with the actual evaluation modes used by the already
proved one-spectator positive integral and same-H energy budget. -/
theorem actual_evaluation_occupation_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) :
    HasSum (fun j => thermalEigenvalue a j * occupationMetricNormSq (fun _ => 1)
      (modeAnnihilate (rawJetMode G theta j R) p))
      (∫ beta, thermalWeight a beta * occupationMetricNormSq (fun _ => 1)
        (modeAnnihilate (evaluationCoordinates G theta (R+beta)) p) ∂planeMeasure) := by
  simpa only [evaluationCoordinates_eq_rawJetCoordinates, rawJetMode] using
    actual_rawJet_occupation_hasSum G theta hG a ha R p

/-- With the original pair-removal anchor inserted, the inner offset integral
is the genuine one-spectator spectral series, on the same polynomial core. -/
theorem actual_anchored_oneSpectator_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) :
    HasSum (fun j => thermalEigenvalue a j * occupationMetricNormSq (fun _ => 1)
      (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) p)))
      (∫ beta, thermalWeight a beta * occupationMetricNormSq (fun _ => 1)
        (modeAnnihilate (evaluationCoordinates G theta (R+beta))
          (modePair (evaluationCoordinates G theta R) p)) ∂planeMeasure) :=
  actual_evaluation_occupation_hasSum G theta hG a ha R _

end TorusLean.Shared.ThermalCoherentSpectralOccupation
