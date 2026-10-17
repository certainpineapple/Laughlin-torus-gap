import torus.shared.ThermalCoherentDoubleOccupation
import torus.shared.ThermalCoherentDoubleGaussian
import torus.shared.ThermalCoherentDoubleRegularity

/-! The positive double-offset integral with exactly the paper's explicit
1/2 spectator normalization, bounded by the same actual H and S4.
This file proves neither its equality with an Omega4 thermal transfer nor
the Sym²/COM identities that would identify the transfer normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentDoubleIntegral
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonPolarization TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonFullContact
open TorusLean.Shared.PhysicalBosonAnchor TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Shared.ThermalCoherentGaussian TorusLean.Shared.ThermalCoherentDoubleOccupation
open TorusLean.Shared.ThermalCoherentDoubleGaussian TorusLean.Shared.ThermalCoherentDoubleRegularity
open TorusLean.Boson.PhysicalContactLiftCandidate TorusLean.Fermion.LatticePacking

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩
local instance : SFinite planeMeasure := by
  unfold planeMeasure
  infer_instance

/-- The half-normalized double-spectator bound after actual pair removal. -/
def doubleAnchorBudget (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R : ℂ) : ℝ :=
  let b := modePair (evaluationCoordinates G theta R) p
  sAllowance^2 * (2 * cAllowance * (occupationInner (fun _ => 1) b
    (contactCoreHamiltonian G theta b)).re + occupationMetricNormSq (fun _ => 1) b)

theorem doubleAnchorBudget_integrable (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (doubleAnchorBudget G theta p) (cellMeasure G 2) :=
  (((modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta) p).re.const_mul
    (2*cAllowance)).add (modePair_normSq_integrable G theta p)).const_mul (sAllowance^2)

/-- The single explicit 1/2 is paid here; no COM 2/4 factor is introduced. -/
theorem half_twoSpectatorNormSq_le_doubleAnchorBudget (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R S T : ℂ)
    (hL : 20 ≤ systole G) :
    (1/2 : ℝ) * twoSpectatorNormSq G theta p R S T ≤ doubleAnchorBudget G theta p R := by
  have h := mul_le_mul_of_nonneg_left
    (raw_evaluation_double_occupation_budget G theta S T
      (modePair (evaluationCoordinates G theta R) p) hL) (by norm_num : (0 : ℝ) ≤ 1/2)
  unfold twoSpectatorNormSq doubleAnchorBudget
  convert h using 1
  ring

/-- Both offsets are integrated against full d²β/π d²γ/π. The factor 1/2
is written explicitly and is not part of either Gaussian marginal. -/
def twoSpectatorIntegrand (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (x : ℂ × (ℂ × ℂ)) : ℝ :=
  thermalProductWeight a x.2 * ((1/2 : ℝ) *
    twoSpectatorNormSq G theta p x.1 (x.1+x.2.1) (x.1+x.2.2))

theorem twoSpectatorIntegrand_eq_exp (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (x : ℂ × (ℂ × ℂ)) :
    twoSpectatorIntegrand G theta a p x = (1/2 : ℝ) *
      Real.exp (-a * (‖x.2.1‖^2 + ‖x.2.2‖^2)) *
        twoSpectatorNormSq G theta p x.1 (x.1+x.2.1) (x.1+x.2.2) := by
  rw [twoSpectatorIntegrand, thermalProductWeight_eq_exp]
  ring

theorem twoSpectatorIntegrand_nonneg (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (x : ℂ × (ℂ × ℂ)) :
    0 ≤ twoSpectatorIntegrand G theta a p x :=
  mul_nonneg (thermalProductWeight_pos a x.2).le
    (mul_nonneg (by norm_num) (twoSpectatorNormSq_nonneg G theta p _ _ _))

theorem twoSpectatorIntegrand_continuous (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Continuous (twoSpectatorIntegrand G theta a p) :=
  ((thermalProductWeight_continuous a).comp continuous_snd).mul
    ((twoSpectatorOffset_continuous G theta p).const_mul (1/2 : ℝ))

/-- Joint integrability in the anchor and both whole-plane offsets. -/
theorem twoSpectatorIntegrand_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    Integrable (twoSpectatorIntegrand G theta a p)
      ((cellMeasure G 2).prod (planeMeasure.prod planeMeasure)) := by
  apply ((doubleAnchorBudget_integrable G theta p).mul_prod
    (thermalProductWeight_integrable a ha)).mono'
    (twoSpectatorIntegrand_continuous G theta a p).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (twoSpectatorIntegrand_nonneg G theta a p x)]
  change thermalProductWeight a x.2 * ((1/2 : ℝ) *
    twoSpectatorNormSq G theta p x.1 (x.1+x.2.1) (x.1+x.2.2)) ≤ _
  rw [mul_comm (doubleAnchorBudget G theta p x.1)]
  exact mul_le_mul_of_nonneg_left
    (half_twoSpectatorNormSq_le_doubleAnchorBudget G theta p _ _ _ hL)
    (thermalProductWeight_pos a x.2).le

/-- Every fixed-anchor double-offset slice is integrable. -/
theorem twoSpectator_inner_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (R : ℂ) (hL : 20 ≤ systole G) :
    Integrable (fun y => twoSpectatorIntegrand G theta a p (R,y))
      (planeMeasure.prod planeMeasure) := by
  apply ((thermalProductWeight_integrable a ha).mul_const (doubleAnchorBudget G theta p R)).mono'
    ((twoSpectatorIntegrand_continuous G theta a p).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  change ‖twoSpectatorIntegrand G theta a p (R,y)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (twoSpectatorIntegrand_nonneg G theta a p (R,y))]
  exact mul_le_mul_of_nonneg_left
    (half_twoSpectatorNormSq_le_doubleAnchorBudget G theta p _ _ _ hL)
    (thermalProductWeight_pos a y).le

/-- Even the innermost gamma slice is integrable for every anchor and beta. -/
theorem twoSpectator_last_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (R β : ℂ) (hL : 20 ≤ systole G) :
    Integrable (fun γ => twoSpectatorIntegrand G theta a p (R,(β,γ))) planeMeasure := by
  have hc : Continuous (fun γ : ℂ => twoSpectatorIntegrand G theta a p (R,(β,γ))) :=
    Continuous.comp (g := twoSpectatorIntegrand G theta a p)
      (f := fun γ : ℂ => (R,(β,γ)))
      (twoSpectatorIntegrand_continuous G theta a p)
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  apply ((thermalWeight_integrable a ha).mul_const
    (thermalWeight a β * doubleAnchorBudget G theta p R)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro γ
  rw [Real.norm_eq_abs, abs_of_nonneg (twoSpectatorIntegrand_nonneg G theta a p (R,(β,γ)))]
  calc
    _ ≤ thermalProductWeight a (β,γ) * doubleAnchorBudget G theta p R :=
      mul_le_mul_of_nonneg_left
        (half_twoSpectatorNormSq_le_doubleAnchorBudget G theta p _ _ _ hL)
        (thermalProductWeight_pos a (β,γ)).le
    _ = _ := by unfold thermalProductWeight; ring

theorem twoSpectator_inner_eq_iterated (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (R : ℂ) (hL : 20 ≤ systole G) :
    (∫ y, twoSpectatorIntegrand G theta a p (R,y) ∂planeMeasure.prod planeMeasure) =
      ∫ β, (∫ γ, twoSpectatorIntegrand G theta a p (R,(β,γ)) ∂planeMeasure) ∂planeMeasure :=
  integral_prod _ (twoSpectator_inner_integrable G theta a ha p R hL)

def twoSpectatorForm (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, (∫ y, twoSpectatorIntegrand G theta a p (R,y)
    ∂planeMeasure.prod planeMeasure) ∂cellMeasure G 2

theorem twoSpectator_outer_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    Integrable (fun R => ∫ y, twoSpectatorIntegrand G theta a p (R,y)
      ∂planeMeasure.prod planeMeasure) (cellMeasure G 2) :=
  (twoSpectatorIntegrand_integrable G theta a ha p hL).integral_prod_left

/-- Exact original iterated positive expression, exposing the sole 1/2
and keeping both offsets on the full plane. -/
theorem twoSpectatorForm_eq_iterated (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    twoSpectatorForm G theta a p = (1/2 : ℝ) *
      ∫ R, (∫ β, (∫ γ, Real.exp (-a * (‖β‖^2 + ‖γ‖^2)) *
        twoSpectatorNormSq G theta p R (R+β) (R+γ) ∂planeMeasure) ∂planeMeasure)
          ∂cellMeasure G 2 := by
  unfold twoSpectatorForm
  simp_rw [twoSpectator_inner_eq_iterated G theta a ha p _ hL,
    twoSpectatorIntegrand_eq_exp, mul_assoc, integral_const_mul]

theorem twoSpectatorForm_nonneg (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    0 ≤ twoSpectatorForm G theta a p :=
  integral_nonneg (fun R => integral_nonneg (fun y => twoSpectatorIntegrand_nonneg G theta a p (R,y)))

theorem twoSpectator_inner_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (R : ℂ) (hL : 20 ≤ systole G) :
    (∫ y, twoSpectatorIntegrand G theta a p (R,y) ∂planeMeasure.prod planeMeasure) ≤
      (1/a^2) * doubleAnchorBudget G theta p R := by
  calc
    _ ≤ ∫ y, thermalProductWeight a y * doubleAnchorBudget G theta p R
        ∂planeMeasure.prod planeMeasure := by
      apply integral_mono (twoSpectator_inner_integrable G theta a ha p R hL)
        ((thermalProductWeight_integrable a ha).mul_const _)
      intro y
      exact mul_le_mul_of_nonneg_left
        (half_twoSpectatorNormSq_le_doubleAnchorBudget G theta p _ _ _ hL)
        (thermalProductWeight_pos a y).le
    _ = _ := by rw [integral_mul_const, thermalProductWeight_integral a ha]

/-- Exact double Gaussian mass and one explicit half-normalization give
s²/a² (2c times actual output-sector H + the actual original-sector H). -/
theorem twoSpectatorForm_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hL : 20 ≤ systole G) :
    twoSpectatorForm G theta a p ≤ (sAllowance^2/a^2) *
      (2*cAllowance * (∫ R, (occupationInner (fun _ => 1)
        (modePair (evaluationCoordinates G theta R) p)
        (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re
          ∂cellMeasure G 2) +
       (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re) := by
  calc
    _ ≤ ∫ R, (1/a^2) * doubleAnchorBudget G theta p R ∂cellMeasure G 2 :=
      integral_mono (twoSpectator_outer_integrable G theta a ha p hL)
        ((doubleAnchorBudget_integrable G theta p).const_mul (1/a^2))
        (fun R => twoSpectator_inner_bound G theta a ha p R hL)
    _ = _ := by
      have he : Integrable (fun R => (occupationInner (fun _ => 1)
        (modePair (evaluationCoordinates G theta R) p)
        (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))).re)
          (cellMeasure G 2) :=
        (modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta) p).re
      rw [integral_const_mul]
      simp only [doubleAnchorBudget]
      rw [integral_const_mul, integral_add (he.const_mul (2*cAllowance))
        (modePair_normSq_integrable G theta p), integral_const_mul,
        integrated_modePair_normSq_same_lift]
      ring

def actualTwoSpectatorForm (G : Geometry) (theta : Twist) (a : ℝ) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) : ℝ :=
  twoSpectatorForm G theta a ((physicalSectorEquiv G theta M).symm f).val

theorem actualTwoSpectatorForm_pairOutput_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (N : ℕ) (f : PhysicalBosonCarrier G theta (N+2))
    (hL : 20 ≤ systole G) :
    actualTwoSpectatorForm G theta a (N+2) f ≤ (sAllowance^2/a^2) *
      (2*cAllowance * (∫ R, actualParticleContactEnergy G N
        (physicalPairSection G theta N R f).val ∂cellMeasure G 2) +
        actualParticleContactEnergy G (N+2) f.val) := by
  simpa only [actualTwoSpectatorForm, fullCarrier_contact_energy_same_lift,
    physicalPairSection_coordinates] using twoSpectatorForm_bound G theta a ha
      ((physicalSectorEquiv G theta (N+2)).symm f).val hL

theorem actualTwoSpectatorForm_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20 ≤ systole G) :
    actualTwoSpectatorForm G theta a ((N+2)+2) f ≤ (sAllowance^2/a^2) *
      (2*cAllowance * actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) := by
  have h := actualTwoSpectatorForm_pairOutput_bound G theta a ha (N+2) f hL
  rwa [physical_output_energy_anchor_S4] at h

#print axioms half_twoSpectatorNormSq_le_doubleAnchorBudget
#print axioms twoSpectatorIntegrand_integrable
#print axioms twoSpectator_inner_integrable
#print axioms twoSpectator_last_integrable
#print axioms twoSpectator_inner_eq_iterated
#print axioms twoSpectator_outer_integrable
#print axioms twoSpectatorForm_eq_iterated
#print axioms twoSpectatorForm_bound
#print axioms actualTwoSpectatorForm_pairOutput_bound
#print axioms actualTwoSpectatorForm_bound
end TorusLean.Shared.ThermalCoherentDoubleIntegral
