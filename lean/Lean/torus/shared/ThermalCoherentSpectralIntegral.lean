import torus.shared.ThermalCoherentSpectralIntegralPositive
import torus.shared.ThermalCoherentSpectralOccupation
import torus.shared.ThermalCoherentIntegral

/-! The already defined positive one-spectator form equals its actual
all-level raw-jet spectral series. The original joint integrability controls
the positive anchor sum/integral interchange; the unchanged H/S4 bound is
then inherited. This is not an identification with an Omega or COM form. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSpectralIntegral
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.ThermalCoherentRegularity TorusLean.Shared.ThermalCoherentIntegral
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.ThermalCoherentMoments
open TorusLean.Shared.PlaneJetParameterContinuity TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open scoped ComplexConjugate BigOperators

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- Actual spectator raw jet after the unchanged normalized pair anchor. -/
def anchoredJetNormSq (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (j : ℕ) (R : ℂ) : ℝ :=
  occupationMetricNormSq (fun _ => 1)
    (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) p))

theorem anchoredJetNormSq_nonneg (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (j : ℕ) (R : ℂ) :
    0 ≤ anchoredJetNormSq G theta p j R := occupationMetricNormSq_nonneg _ _

theorem anchoredJetNormSq_continuous (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (j : ℕ) :
    Continuous (anchoredJetNormSq G theta p j) := by
  let c : (TwoBodyLift.PairIndex (OrbitalIndex G theta) × OrbitalIndex G theta) → ℂ → ℂ :=
    fun t R => pairProduct G theta t.1.1 t.1.2 R * conj (rawJetMode G theta j R t.2)
  let v : (TwoBodyLift.PairIndex (OrbitalIndex G theta) × OrbitalIndex G theta) →
      Core (OrbitalIndex G theta) ℂ := fun t => annihilate t.2 (TwoBodyLift.pairRemove t.1 p)
  have hcoord (i : OrbitalIndex G theta) : Continuous (fun R => rawJetMode G theta j R i) := by
    simp only [rawJetMode, OrthonormalBasis.repr_apply_apply]
    exact continuous_const.inner (rawPlaneJet_continuous G theta j)
  have hc (t) : Continuous (c t) :=
    (pairProduct_continuous G theta t.1.1 t.1.2).mul
      (Complex.continuous_conj.comp (hcoord t.2))
  have he (R : ℂ) : modeAnnihilate (rawJetMode G theta j R)
      (modePair (evaluationCoordinates G theta R) p) = ∑ t, c t R • v t := by
    rw [modePair_evaluation_expansion]
    simp only [map_sum, map_smul, modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type, c, v, Complex.star_def]
  change Continuous (fun R => occupationMetricNormSq (fun _ => 1)
    (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) p)))
  simp_rw [he]
  exact finite_combination_normSq_continuous c hc v

private theorem anchored_spectral_pointwise (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) (R : ℂ) :
    HasSum (fun j => thermalEigenvalue a j * anchoredJetNormSq G theta p j R)
      (∫ beta, oneSpectatorIntegrand G theta a p (R,beta) ∂planeMeasure) :=
  actual_anchored_oneSpectator_hasSum G theta (by linarith) a ha R p

theorem weighted_anchoredJetNormSq_integrable (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) (j : ℕ) :
    Integrable (fun R => thermalEigenvalue a j * anchoredJetNormSq G theta p j R)
      (cellMeasure G 2) :=
  nonnegative_hasSum_term_integrable (cellMeasure G 2)
    (fun j R => thermalEigenvalue a j * anchoredJetNormSq G theta p j R) _
    (fun j R => mul_nonneg (thermalEigenvalue_pos a ha j).le (anchoredJetNormSq_nonneg G theta p j R))
    (fun j => ((anchoredJetNormSq_continuous G theta p j).const_mul _).aestronglyMeasurable)
    (anchored_spectral_pointwise G theta a ha p hL)
    (oneSpectator_outer_integrable G theta a ha p hL) j

theorem anchoredJetNormSq_integrable (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) (j : ℕ) :
    Integrable (anchoredJetNormSq G theta p j) (cellMeasure G 2) := by
  have h := (weighted_anchoredJetNormSq_integrable G theta a ha p hL j).const_mul
    (thermalEigenvalue a j)⁻¹
  apply h.congr
  exact Filter.Eventually.of_forall fun R => by
    dsimp only
    rw [inv_mul_cancel_left₀ (thermalEigenvalue_pos a ha j).ne']

/-- True positive spectral transport through the outer anchor integral. -/
theorem oneSpectatorForm_spectral_hasSum (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    HasSum (fun j => thermalEigenvalue a j *
      ∫ R, anchoredJetNormSq G theta p j R ∂cellMeasure G 2)
      (oneSpectatorForm G theta a p) := by
  have h := integral_hasSum_of_nonnegative_hasSum (cellMeasure G 2)
    (fun j R => thermalEigenvalue a j * anchoredJetNormSq G theta p j R) _
    (fun j R => mul_nonneg (thermalEigenvalue_pos a ha j).le (anchoredJetNormSq_nonneg G theta p j R))
    (fun j => ((anchoredJetNormSq_continuous G theta p j).const_mul _).aestronglyMeasurable)
    (anchored_spectral_pointwise G theta a ha p hL)
    (oneSpectator_outer_integrable G theta a ha p hL)
  simpa only [integral_const_mul, oneSpectatorForm] using h

theorem oneSpectatorForm_eq_spectral (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    oneSpectatorForm G theta a p = ∑' j, thermalEigenvalue a j *
      ∫ R, anchoredJetNormSq G theta p j R ∂cellMeasure G 2 :=
  (oneSpectatorForm_spectral_hasSum G theta a ha p hL).tsum_eq.symm

/-- The positive series is bounded by the same actual pair-output energy
and contact H, with the already proved N-independent coefficient. -/
theorem oneSpectral_sum_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    (∑' j, thermalEigenvalue a j * ∫ R, anchoredJetNormSq G theta p j R ∂cellMeasure G 2) ≤
      (sAllowance/a) * (cAllowance * (∫ R, (occupationInner (fun _ => 1)
        (modePair (evaluationCoordinates G theta R) p)
        (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re
          ∂cellMeasure G 2) +
        (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re) := by
  rw [← oneSpectatorForm_eq_spectral G theta a ha p hL]
  exact oneSpectatorForm_bound G theta a ha p hL

/-- On the original full physical carrier this is the literal H and S4
bound, not a norm bound paid with particle number. -/
theorem actual_oneSpectral_sum_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20 ≤ systole G) :
    (∑' j, thermalEigenvalue a j * ∫ R, anchoredJetNormSq G theta
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val j R ∂cellMeasure G 2) ≤
        (sAllowance/a) * (cAllowance * actualPositiveFourBodyForm G theta N f +
          actualParticleContactEnergy G ((N+2)+2) f.val) := by
  rw [← oneSpectatorForm_eq_spectral G theta a ha _ hL]
  exact actualOneSpectatorForm_bound G theta a ha N f hL

end TorusLean.Shared.ThermalCoherentSpectralIntegral
