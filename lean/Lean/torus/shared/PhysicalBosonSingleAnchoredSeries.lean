import torus.shared.BosonAnchoredExteriorIntegral
import torus.shared.BosonAnchoredAbsoluteIntegral
import torus.shared.ThermalCoherentAnchoredCOMSummability

set_option autoImplicit false
noncomputable section
open TorusLean.Boson.SpectatorControl
namespace TorusLean.Shared.PhysicalBosonSingleAnchoredSeries
open MeasureTheory TorusLean.Boson TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonSingleExterior TorusLean.Shared.BosonAnchoredExteriorIntegral
open TorusLean.Shared.BosonAnchoredAbsoluteIntegral TorusLean.Shared.BosonAnchoredKRows
open TorusLean.Fermion.LatticePacking
open scoped BigOperators

/-- The original physical single-contraction form is the sum of the genuine
anchored-K block forms. Both scalar full-plane and outer-cell exchanges
are derived from absolute integrability before this identification. -/
theorem original_singleContraction_anchored_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (N M : ℕ) (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) (hg : g.IsHomogeneous (M+3)) :
    HasSum (fun l => anchoredBlockForm G theta l f g)
      (ip f (TorusLean.Shared.BosonLiftSquare.contractionLift
        (TorusLean.Boson.PhysicalContactLiftCandidate.contactPairCoordinates G theta)
        TorusLean.Shared.BosonPairContractions.singleContraction g)) := by
  have hs := anchoredBlockForm_hasSum_integral G theta hG N M f g hf hg
  rw [original_singleContraction_plane_integral]
  convert hs using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  exact (original_plane_kernel_rank_hasSum G theta hG f g R).tsum_eq.symm

open TorusLean.Shared.ThermalCoherentAnchoredCOMSummability

/-- Actual original S3 equals the signed relative H-squared-minus-H spectrum.
The two infinite rearrangements use independent proved absolute bounds. -/
theorem original_singleContraction_relative_series (G : Geometry) (theta : Twist)
    (hG : 20 ≤ systole G) (N M : ℕ) (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) (hg : g.IsHomogeneous (M+3)) :
    ip f (TorusLean.Shared.BosonLiftSquare.contractionLift
        (TorusLean.Boson.PhysicalContactLiftCandidate.contactPairCoordinates G theta)
        TorusLean.Shared.BosonPairContractions.singleContraction g) =
      ∑' d, ((2*(-1/2:ℝ)^d : ℝ) : ℂ)*anchoredRelativeCross G theta d f g := by
  have hs := original_singleContraction_anchored_hasSum G theta
    (le_trans (by norm_num : (1:ℝ) ≤ 20) hG) N M f g hf hg
  have hc := anchoredCOM_antidiagonal_hasSum G theta f g hG
  have he : (fun l => anchoredBlockForm G theta l f g) =
      (fun l => ∑ d ∈ Finset.range (l+1),
        (ThermalCoherentJacobiAnchored.anchoredJacobiCrossWeight d (l-d) : ℂ) *
          anchoredRelativeCross G theta d f g) := by
    funext l
    exact anchoredBlockForm_finite_COM G theta l f g
  rw [he] at hs
  exact hs.unique hc

end TorusLean.Shared.PhysicalBosonSingleAnchoredSeries
