import torus.shared.ThermalCoherentSpectralDouble
import torus.shared.ThermalCoherentSpectralIntegral

/-! Outer-anchor transport of the genuine ordered double thermal spectrum.
The original jointly integrable two-spectator form dominates every positive
spectral term. Its same-H/S4 bound is inherited with the unique Sym2 half.
No identification with Omega4, a COM transfer, or an unweighted limit is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSpectralDouble
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonS4 TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Shared.ThermalCoherentRegularity TorusLean.Shared.ThermalCoherentDoubleIntegral
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.ThermalCoherentMoments
open TorusLean.Shared.ThermalCoherentSpectralIntegral
open TorusLean.Shared.PlaneJetParameterContinuity TorusLean.Shared.PlaneJetMembership
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open scoped ComplexConjugate BigOperators

local instance integral_physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- The two raw spectator jets following the unchanged pair anchor. -/
def anchoredDoubleJetNormSq (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (jm : ℕ × ℕ) (R : ℂ) : ℝ :=
  doubleJetNormSq G theta R (modePair (evaluationCoordinates G theta R) p) jm

theorem anchoredDoubleJetNormSq_nonneg (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (jm : ℕ × ℕ) (R : ℂ) :
    0 ≤ anchoredDoubleJetNormSq G theta p jm R := doubleJetNormSq_nonneg _ _ _ _ _

theorem anchoredDoubleJetNormSq_continuous (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (jm : ℕ × ℕ) :
    Continuous (anchoredDoubleJetNormSq G theta p jm) := by
  let c : (TwoBodyLift.PairIndex (OrbitalIndex G theta) ×
      (OrbitalIndex G theta × OrbitalIndex G theta)) → ℂ → ℂ := fun t R =>
    pairProduct G theta t.1.1 t.1.2 R * conj (rawJetMode G theta jm.1 R t.2.1) *
      conj (rawJetMode G theta jm.2 R t.2.2)
  let v : (TwoBodyLift.PairIndex (OrbitalIndex G theta) ×
      (OrbitalIndex G theta × OrbitalIndex G theta)) → Core (OrbitalIndex G theta) ℂ :=
    fun t => annihilate t.2.2 (annihilate t.2.1 (TwoBodyLift.pairRemove t.1 p))
  have hcoord (j : ℕ) (i : OrbitalIndex G theta) :
      Continuous (fun R => rawJetMode G theta j R i) := by
    simp only [rawJetMode, OrthonormalBasis.repr_apply_apply]
    exact continuous_const.inner (rawPlaneJet_continuous G theta j)
  have hc (t) : Continuous (c t) :=
    ((pairProduct_continuous G theta t.1.1 t.1.2).mul
      (Complex.continuous_conj.comp (hcoord jm.1 t.2.1))).mul
      (Complex.continuous_conj.comp (hcoord jm.2 t.2.2))
  have he (R : ℂ) : modeAnnihilate (rawJetMode G theta jm.2 R)
      (modeAnnihilate (rawJetMode G theta jm.1 R)
        (modePair (evaluationCoordinates G theta R) p)) = ∑ t, c t R • v t := by
    rw [modePair_evaluation_expansion]
    simp only [map_sum, map_smul, modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type, c, v, Complex.star_def, mul_assoc]
  change Continuous (fun R => occupationMetricNormSq (fun _ => 1)
    (modeAnnihilate (rawJetMode G theta jm.2 R)
      (modeAnnihilate (rawJetMode G theta jm.1 R)
        (modePair (evaluationCoordinates G theta R) p))))
  simp_rw [he]
  exact finite_combination_normSq_continuous c hc v

theorem weighted_anchoredDoubleJetNormSq_integrable (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G)
    (jm : ℕ × ℕ) :
    Integrable (fun R => (1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
      anchoredDoubleJetNormSq G theta p jm R)) (cellMeasure G 2) :=
  nonnegative_hasSum_term_integrable (cellMeasure G 2)
    (fun jm R => (1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
      anchoredDoubleJetNormSq G theta p jm R)) _
    (fun jm R => mul_nonneg (by positivity) (mul_nonneg
      (mul_nonneg (thermalEigenvalue_pos a ha jm.1).le (thermalEigenvalue_pos a ha jm.2).le)
      (anchoredDoubleJetNormSq_nonneg G theta p jm R)))
    (fun jm => (((anchoredDoubleJetNormSq_continuous G theta p jm).const_mul _).const_mul
      (1/2 : ℝ)).aestronglyMeasurable)
    (fun R => anchoredDoubleThermal_hasSum G theta a ha R p hL)
    (twoSpectator_outer_integrable G theta a ha p hL) jm

theorem anchoredDoubleJetNormSq_integrable (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G)
    (jm : ℕ × ℕ) :
    Integrable (anchoredDoubleJetNormSq G theta p jm) (cellMeasure G 2) := by
  let C := (1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2)
  have hC : C ≠ 0 := ne_of_gt (mul_pos (by norm_num)
    (mul_pos (thermalEigenvalue_pos a ha jm.1) (thermalEigenvalue_pos a ha jm.2)))
  have h := (weighted_anchoredDoubleJetNormSq_integrable G theta a ha p hL jm).const_mul C⁻¹
  apply h.congr
  exact Filter.Eventually.of_forall fun R => by
    change C⁻¹ * ((1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 * _)) = _
    rw [← mul_assoc (1/2 : ℝ)]
    exact inv_mul_cancel_left₀ hC _

/-- The complete ordered positive series equals the original anchor form. -/
theorem twoSpectatorForm_spectral_hasSum (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    HasSum (fun jm : ℕ × ℕ => (1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
      ∫ R, anchoredDoubleJetNormSq G theta p jm R ∂cellMeasure G 2))
      (twoSpectatorForm G theta a p) := by
  have h := integral_hasSum_of_nonnegative_hasSum (cellMeasure G 2)
    (fun jm R => (1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
      anchoredDoubleJetNormSq G theta p jm R)) _
    (fun jm R => mul_nonneg (by positivity) (mul_nonneg
      (mul_nonneg (thermalEigenvalue_pos a ha jm.1).le (thermalEigenvalue_pos a ha jm.2).le)
      (anchoredDoubleJetNormSq_nonneg G theta p jm R)))
    (fun jm => (((anchoredDoubleJetNormSq_continuous G theta p jm).const_mul _).const_mul
      (1/2 : ℝ)).aestronglyMeasurable)
    (fun R => anchoredDoubleThermal_hasSum G theta a ha R p hL)
    (twoSpectator_outer_integrable G theta a ha p hL)
  simpa only [integral_const_mul, twoSpectatorForm] using h

theorem twoSpectatorForm_eq_spectral (G : Geometry) (theta : Twist)
    (a : ℝ) (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    twoSpectatorForm G theta a p = ∑' jm : ℕ × ℕ, (1/2 : ℝ) *
      (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
        ∫ R, anchoredDoubleJetNormSq G theta p jm R ∂cellMeasure G 2) :=
  (twoSpectatorForm_spectral_hasSum G theta a ha p hL).tsum_eq.symm

theorem doubleSpectral_sum_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    (∑' jm : ℕ × ℕ, (1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
      ∫ R, anchoredDoubleJetNormSq G theta p jm R ∂cellMeasure G 2)) ≤
      (sAllowance^2/a^2) * (2*cAllowance * (∫ R, (occupationInner (fun _ => 1)
        (modePair (evaluationCoordinates G theta R) p)
        (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re
          ∂cellMeasure G 2) +
        (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re) := by
  rw [← twoSpectatorForm_eq_spectral G theta a ha p hL]
  exact twoSpectatorForm_bound G theta a ha p hL

theorem actual_doubleSpectral_sum_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20 ≤ systole G) :
    (∑' jm : ℕ × ℕ, (1/2 : ℝ) * (thermalEigenvalue a jm.1 * thermalEigenvalue a jm.2 *
      ∫ R, anchoredDoubleJetNormSq G theta
        ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val jm R ∂cellMeasure G 2)) ≤
      (sAllowance^2/a^2) * (2*cAllowance * actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) := by
  rw [← twoSpectatorForm_eq_spectral G theta a ha _ hL]
  exact actualTwoSpectatorForm_bound G theta a ha N f hL

end TorusLean.Shared.ThermalCoherentSpectralDouble
