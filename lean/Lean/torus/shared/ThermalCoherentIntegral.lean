import torus.shared.ThermalCoherentOccupation
import torus.shared.ThermalCoherentGaussian
import torus.shared.ThermalCoherentRegularity

/-! Actual positive one-spectator coherent integral and an N-independent
bound by the unchanged Hamiltonian and output-sector Hamiltonian.
This is the right-hand side of the paper's one-spectator transfer identity;
identifying it with a transferred infinite relative thermal coefficient is
not claimed here. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentIntegral
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonPolarization TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonFullContact TorusLean.Shared.PhysicalBosonAnchor
open TorusLean.Shared.PhysicalBosonS4 TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Shared.ThermalCoherentOccupation TorusLean.Shared.ThermalCoherentGaussian
open TorusLean.Shared.ThermalCoherentRegularity TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Boson.PhysicalContactLiftCandidate TorusLean.Fermion.LatticePacking

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

local instance : SFinite planeMeasure := by
  unfold planeMeasure
  infer_instance

/-- The bound in the sector after the genuine pair annihilator. -/
def anchorBudget (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R : ℂ) : ℝ :=
  let b := modePair (evaluationCoordinates G theta R) p
  sAllowance * (cAllowance * (occupationInner (fun _ => 1) b
    (contactCoreHamiltonian G theta b)).re + occupationMetricNormSq (fun _ => 1) b)

theorem anchorBudget_integrable (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (anchorBudget G theta p) (cellMeasure G 2) :=
  (((modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta) p).re.const_mul
    cAllowance).add (modePair_normSq_integrable G theta p)).const_mul sAllowance

theorem oneSpectatorNormSq_le_anchorBudget (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R S : ℂ)
    (hL : 20 ≤ systole G) : oneSpectatorNormSq G theta p R S ≤ anchorBudget G theta p R :=
  raw_evaluation_occupation_budget G theta S (modePair (evaluationCoordinates G theta R) p) hL

/-- Positive integrand on cell × the ENTIRE offset plane. -/
def oneSpectatorIntegrand (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (x : ℂ × ℂ) : ℝ :=
  thermalWeight a x.2 * oneSpectatorNormSq G theta p x.1 (x.1 + x.2)

theorem oneSpectatorIntegrand_nonneg (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (x : ℂ × ℂ) :
    0 ≤ oneSpectatorIntegrand G theta a p x :=
  mul_nonneg (thermalWeight_pos a x.2).le (oneSpectatorNormSq_nonneg G theta p _ _)

theorem oneSpectatorIntegrand_continuous (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Continuous (oneSpectatorIntegrand G theta a p) :=
  ((thermalWeight_continuous a).comp continuous_snd).mul (oneSpectatorOffset_continuous G theta p)

/-- A genuine integrability proof for the joint positive kernel. -/
theorem oneSpectatorIntegrand_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    Integrable (oneSpectatorIntegrand G theta a p) ((cellMeasure G 2).prod planeMeasure) := by
  apply ((anchorBudget_integrable G theta p).mul_prod (thermalWeight_integrable a ha)).mono'
    (oneSpectatorIntegrand_continuous G theta a p).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (oneSpectatorIntegrand_nonneg G theta a p x)]
  change thermalWeight a x.2 * oneSpectatorNormSq G theta p x.1 (x.1 + x.2) ≤ _
  rw [mul_comm (anchorBudget G theta p x.1)]
  exact mul_le_mul_of_nonneg_left (oneSpectatorNormSq_le_anchorBudget G theta p _ _ hL)
    (thermalWeight_pos a x.2).le

/-- Every offset slice is integrable, not merely almost every anchor slice. -/
theorem oneSpectator_inner_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (R : ℂ) (hL : 20 ≤ systole G) :
    Integrable (fun β => oneSpectatorIntegrand G theta a p (R,β)) planeMeasure := by
  apply ((thermalWeight_integrable a ha).mul_const (anchorBudget G theta p R)).mono'
    ((oneSpectatorIntegrand_continuous G theta a p).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro β
  change ‖oneSpectatorIntegrand G theta a p (R,β)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (oneSpectatorIntegrand_nonneg G theta a p (R,β))]
  exact mul_le_mul_of_nonneg_left (oneSpectatorNormSq_le_anchorBudget G theta p _ _ hL)
    (thermalWeight_pos a β).le

def oneSpectatorForm (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, (∫ β, oneSpectatorIntegrand G theta a p (R,β) ∂planeMeasure) ∂cellMeasure G 2

theorem oneSpectator_outer_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    Integrable (fun R => ∫ β, oneSpectatorIntegrand G theta a p (R,β) ∂planeMeasure)
      (cellMeasure G 2) := (oneSpectatorIntegrand_integrable G theta a ha p hL).integral_prod_left

theorem oneSpectatorForm_nonneg (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    0 ≤ oneSpectatorForm G theta a p :=
  integral_nonneg (fun R => integral_nonneg (fun β => oneSpectatorIntegrand_nonneg G theta a p (R,β)))

theorem oneSpectator_inner_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (R : ℂ) (hL : 20 ≤ systole G) :
    (∫ β, oneSpectatorIntegrand G theta a p (R,β) ∂planeMeasure) ≤
      (1/a) * anchorBudget G theta p R := by
  calc
    _ ≤ ∫ β, thermalWeight a β * anchorBudget G theta p R ∂planeMeasure := by
      apply integral_mono (oneSpectator_inner_integrable G theta a ha p R hL)
        ((thermalWeight_integrable a ha).mul_const _)
      intro β
      exact mul_le_mul_of_nonneg_left (oneSpectatorNormSq_le_anchorBudget G theta p _ _ hL)
        (thermalWeight_pos a β).le
    _ = _ := by rw [integral_mul_const, thermalWeight_integral a ha]

/-- No particle-number constant: exact Gaussian mass times the two genuine
pair-anchor energies, with no extra factor on the pair anchor. -/
theorem oneSpectatorForm_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    oneSpectatorForm G theta a p ≤ (sAllowance/a) *
      (cAllowance * (∫ R, (occupationInner (fun _ => 1)
        (modePair (evaluationCoordinates G theta R) p)
        (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re
          ∂cellMeasure G 2) +
       (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re) := by
  calc
    _ ≤ ∫ R, (1/a) * anchorBudget G theta p R ∂cellMeasure G 2 :=
      integral_mono (oneSpectator_outer_integrable G theta a ha p hL)
        ((anchorBudget_integrable G theta p).const_mul (1/a))
        (fun R => oneSpectator_inner_bound G theta a ha p R hL)
    _ = _ := by
      have he : Integrable (fun R => (occupationInner (fun _ => 1)
        (modePair (evaluationCoordinates G theta R) p)
        (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re)
          (cellMeasure G 2) :=
        (modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta) p).re
      rw [integral_const_mul]
      simp only [anchorBudget]
      rw [integral_const_mul, integral_add (he.const_mul cAllowance)
        (modePair_normSq_integrable G theta p), integral_const_mul,
        integrated_modePair_normSq_same_lift]
      ring

/-- The physical one-spectator form on the independent full bosonic carrier. -/
def actualOneSpectatorForm (G : Geometry) (theta : Twist) (a : ℝ) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) : ℝ :=
  oneSpectatorForm G theta a ((physicalSectorEquiv G theta M).symm f).val

/-- All physical pair-output sectors, including outputs with zero or one
particle, with the actual unchanged contact energy in both sectors. -/
theorem actualOneSpectatorForm_pairOutput_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (N : ℕ) (f : PhysicalBosonCarrier G theta (N+2))
    (hL : 20 ≤ systole G) :
    actualOneSpectatorForm G theta a (N+2) f ≤ (sAllowance/a) *
      (cAllowance * (∫ R, actualParticleContactEnergy G N
        (physicalPairSection G theta N R f).val ∂cellMeasure G 2) +
        actualParticleContactEnergy G (N+2) f.val) := by
  simpa only [actualOneSpectatorForm, fullCarrier_contact_energy_same_lift,
    physicalPairSection_coordinates] using oneSpectatorForm_bound G theta a ha
      ((physicalSectorEquiv G theta (N+2)).symm f).val hL

/-- On N+4 particles both terms are the actual unchanged H and literal S4.
This is not an assumed spectral or Ω3 transfer statement. -/
theorem actualOneSpectatorForm_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20 ≤ systole G) :
    actualOneSpectatorForm G theta a ((N+2)+2) f ≤ (sAllowance/a) *
      (cAllowance * actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) := by
  have h := actualOneSpectatorForm_pairOutput_bound G theta a ha (N+2) f hL
  rwa [physical_output_energy_anchor_S4] at h

#print axioms oneSpectatorIntegrand_integrable
#print axioms oneSpectator_inner_integrable
#print axioms oneSpectator_outer_integrable
#print axioms oneSpectatorForm_bound
#print axioms actualOneSpectatorForm_pairOutput_bound
#print axioms actualOneSpectatorForm_bound
end TorusLean.Shared.ThermalCoherentIntegral
