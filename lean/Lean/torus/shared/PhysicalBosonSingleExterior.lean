import torus.shared.PhysicalBosonSingleDensity
import torus.shared.PhysicalBosonOneEdgeBoundary
import torus.shared.ParameterLadderIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonSingleExterior
open MeasureTheory TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonDiagonal
open TorusLean.Shared.PhysicalBosonSingleDensity TorusLean.Shared.PhysicalBosonOneEdgeBoundary
open scoped BigOperators ComplexConjugate
local instance singleExterior_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def exteriorCoefficient (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R S : ℂ) : ℂ :=
  ip (modeAnnihilate (evaluationCoordinates G theta S)
      (modePair (evaluationCoordinates G theta R) f))
    (modeAnnihilate (evaluationCoordinates G theta R)
      (modePair (evaluationCoordinates G theta S) g))

/-- Expansion of the actual single-contraction exterior coefficient. The
three S-centered orbitals retain their original torus magnetic boundary. -/
theorem exteriorCoefficient_expansion (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R S : ℂ) :
    exteriorCoefficient G theta f g R S =
      ∑ i : PhysicalBosonSector.OrbitalIndex G theta,
      ∑ a : PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        ip (annihilate i (modePair (evaluationCoordinates G theta R) f))
          (modeAnnihilate (evaluationCoordinates G theta R) (pairRemove a g)) *
        exteriorTriple G theta (orbitalBasis G theta a.1)
          (orbitalBasis G theta a.2) (orbitalBasis G theta i) S := by
  classical
  have hmode (q : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
      modeAnnihilate (evaluationCoordinates G theta S) q =
        ∑ i, (orbitalBasis G theta i).val S • annihilate i q := by
    simp only [modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply,
      Complex.star_def, evaluationCoordinates_conj]
  unfold exteriorCoefficient
  rw [hmode, modePair_evaluation_expansion G theta S g]
  simp only [map_sum, map_smul, TwoBodyLift.inner_sum_left, TwoBodyLift.inner_sum_right,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
    Complex.star_def]
  simp only [exteriorTriple, pairProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem exteriorCoefficient_continuous (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R : ℂ) :
    Continuous (exteriorCoefficient G theta f g R) := by
  have he := funext (exteriorCoefficient_expansion G theta f g R)
  rw [he]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro a _
  exact continuous_const.mul (exteriorTriple_continuous G theta
    (orbitalBasis G theta a.1) (orbitalBasis G theta a.2) (orbitalBasis G theta i))


theorem exteriorCoefficient_boundary (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R : ℂ) :
    TorusLean.Geometry.HasLatticeBoundary G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 (exteriorCoefficient G theta f g R) := by
  apply (TorusLean.Geometry.latticeBoundary_iff_forward _ _ _ _ _ _ _).mpr
  intro p S
  have hb (i : PhysicalBosonSector.OrbitalIndex G theta)
      (a : PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :=
    (TorusLean.Geometry.latticeBoundary_iff_forward _ _ _ _ _ _ _).mp
      (exteriorTriple_boundary G theta (orbitalBasis G theta a.1)
        (orbitalBasis G theta a.2) (orbitalBasis G theta i)) p S
  simp_rw [exteriorCoefficient_expansion, hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

open TorusLean.Shared.MagneticBoundaryUnfolding
open TorusLean.Fermion.CanonicalPlaneJets TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.ThermalCoherentOccupation

/-- Actual full moving-mode Gram, including its complex phase. -/
theorem evaluationCoordinates_gram (G : Geometry) (theta : Twist) (R S : ℂ) :
    inner ℂ (evaluationCoordinates G theta R) (evaluationCoordinates G theta S) =
      conj (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 0 R S) := by
  rw [evaluationCoordinates_eq_rawJetCoordinates, evaluationCoordinates_eq_rawJetCoordinates,
    LinearIsometryEquiv.inner_map_map]
  exact groundJetGram_eq_conj_kernel G theta R S

/-- The actual single-contraction exterior polynomial unfolds against the
one internal edge. This leaves every exterior orbital on the original torus. -/
theorem exteriorCoefficient_ground_unfold (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R : ℂ) :
    (∫ S, inner ℂ (evaluationCoordinates G theta R) (evaluationCoordinates G theta S) *
      exteriorCoefficient G theta f g R S ∂cellMeasure G 1) =
    ∫ S, conj (translatedPlaneJet 0 R S) *
      exteriorCoefficient G theta f g R S ∂planeMeasure := by
  have he := cellInner_magneticPeriodization_eq_planeInner G theta
    (exteriorCoefficient G theta f g R) (exteriorCoefficient_continuous G theta f g R)
    (exteriorCoefficient_boundary G theta f g R) (translatedPlaneJet 0 R)
    (TorusLean.Shared.MagneticCellUnfolding.translatedPlaneJet_integrable 0 R)
  have hc := congrArg (starRingEnd ℂ) he
  simp only [cellInner, planeInner, ←integral_conj, map_mul, Complex.conj_conj] at hc
  simpa only [evaluationCoordinates_gram, rawJetFunction, mul_comm] using hc


/-- Exact one-internal-edge unfolding of the original physical single
contraction. The factor four is the original normalized-pair factor two
and the change from the S-cell measure mu2 to the plane measure dA/pi. -/
theorem original_singleContraction_plane_integral (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    ip f (TorusLean.Shared.BosonLiftSquare.contractionLift
      (TorusLean.Boson.PhysicalContactLiftCandidate.contactPairCoordinates G theta)
      TorusLean.Shared.BosonPairContractions.singleContraction g) =
      ∫ R, (4:ℂ) * (∫ S, conj (translatedPlaneJet 0 R S) *
        exteriorCoefficient G theta f g R S ∂planeMeasure) ∂cellMeasure G 2 := by
  rw [original_singleContraction_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  simp only [singleDensity, mul_assoc]
  change (∫ S, (2:ℂ) * (inner ℂ (evaluationCoordinates G theta R)
    (evaluationCoordinates G theta S) * exteriorCoefficient G theta f g R S)
    ∂cellMeasure G 2) = _
  rw [integral_const_mul,
    TorusLean.Shared.ParameterLadderIntegration.cellIntegral_two_eq_charge G 1,
    exteriorCoefficient_ground_unfold]
  norm_num
  ring

end TorusLean.Shared.PhysicalBosonSingleExterior
