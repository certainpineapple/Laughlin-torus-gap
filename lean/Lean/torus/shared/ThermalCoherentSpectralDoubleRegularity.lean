import torus.shared.ThermalCoherentSpectralOccupation
import torus.shared.ThermalCoherentDoubleIntegral

/-! True full-plane joint domains for two spectators on an arbitrary finite
core, before inserting a pair anchor. The unchanged raw two-spectator bound
supplies a Gaussian majorant; finite polynomial expansions give continuity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSpectralDouble
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.ThermalCoherentRegularity TorusLean.Shared.ThermalCoherentDoubleOccupation
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.ThermalCoherentMoments
open TorusLean.Shared.ThermalCoherentGaussian TorusLean.Shared.ThermalCoherentDoubleGaussian
open TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open scoped BigOperators

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩
local instance : SFinite planeMeasure := by unfold planeMeasure; infer_instance

theorem double_evaluation_normSq_continuous (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun x : ℂ × ℂ => occupationMetricNormSq (fun _ => 1)
      (spectatorPair (evaluationCoordinates G theta x.1) (evaluationCoordinates G theta x.2) p)) := by
  let c : (OrbitalIndex G theta × OrbitalIndex G theta) → (ℂ × ℂ) → ℂ :=
    fun ik x => (orbitalBasis G theta ik.1).val x.1 * (orbitalBasis G theta ik.2).val x.2
  let v : (OrbitalIndex G theta × OrbitalIndex G theta) → Core (OrbitalIndex G theta) ℂ :=
    fun ik => annihilate ik.2 (annihilate ik.1 p)
  have hc (ik) : Continuous (c ik) :=
    ((rawLLL_continuous G theta 1 (orbitalBasis G theta ik.1)).comp continuous_fst).mul
      ((rawLLL_continuous G theta 1 (orbitalBasis G theta ik.2)).comp continuous_snd)
  have he (x : ℂ × ℂ) :
      spectatorPair (evaluationCoordinates G theta x.1) (evaluationCoordinates G theta x.2) p =
        ∑ ik, c ik x • v ik := by
    rw [spectatorPair, LinearMap.comp_apply, modeAnnihilate_evaluation_expansion G theta x.1 p]
    simp only [map_sum, map_smul, modeAnnihilate_evaluation_expansion,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type, c, v]
  simpa only [he] using finite_combination_normSq_continuous c hc v

/-- Bare ordered two-spectator density. Sym2 contributes its half later. -/
def bareDoubleThermalIntegrand (G : Geometry) (theta : Twist) (a : ℝ) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × ℂ) : ℝ :=
  thermalProductWeight a x * occupationMetricNormSq (fun _ => 1)
    (spectatorPair (evaluationCoordinates G theta (R+x.1))
      (evaluationCoordinates G theta (R+x.2)) p)

theorem bareDoubleThermalIntegrand_nonneg (G : Geometry) (theta : Twist) (a : ℝ) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × ℂ) :
    0 ≤ bareDoubleThermalIntegrand G theta a R p x :=
  mul_nonneg (thermalProductWeight_pos a x).le (occupationMetricNormSq_nonneg _ _)

theorem bareDoubleThermalIntegrand_continuous (G : Geometry) (theta : Twist) (a : ℝ) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) : Continuous (bareDoubleThermalIntegrand G theta a R p) := by
  have hm : Continuous (fun x : ℂ × ℂ => (R+x.1,R+x.2)) :=
    (continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd)
  have hq := Continuous.comp
    (g := fun x : ℂ × ℂ => occupationMetricNormSq (fun _ => 1)
      (spectatorPair (evaluationCoordinates G theta x.1) (evaluationCoordinates G theta x.2) p))
    (f := fun x : ℂ × ℂ => (R+x.1,R+x.2))
    (double_evaluation_normSq_continuous G theta p) hm
  change Continuous (fun x : ℂ × ℂ => thermalProductWeight a x *
    occupationMetricNormSq (fun _ => 1)
      (spectatorPair (evaluationCoordinates G theta (R+x.1))
        (evaluationCoordinates G theta (R+x.2)) p))
  exact (thermalProductWeight_continuous a).mul hq

/-- Joint full-plane integrability uses the actual raw CCR/same-H bound on p,
not a sector truncation or an assumption that p lies in a pair-removal range. -/
theorem bareDoubleThermalIntegrand_integrable (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0 < a) (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20 ≤ systole G) :
    Integrable (bareDoubleThermalIntegrand G theta a R p) (planeMeasure.prod planeMeasure) := by
  let C := sAllowance^2 * (4*cAllowance *
    (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re +
      2*occupationMetricNormSq (fun _ => 1) p)
  apply ((thermalProductWeight_integrable a ha).mul_const C).mono'
    (bareDoubleThermalIntegrand_continuous G theta a R p).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (bareDoubleThermalIntegrand_nonneg G theta a R p x)]
  exact mul_le_mul_of_nonneg_left
    (raw_evaluation_double_occupation_budget G theta (R+x.1) (R+x.2) p hL)
    (thermalProductWeight_pos a x).le

theorem fixed_rawJet_spectator_normSq_continuous (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (p : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun beta => occupationMetricNormSq (fun _ => 1)
      (modeAnnihilate (rawJetMode G theta j R)
        (modeAnnihilate (evaluationCoordinates G theta (R+beta)) p))) := by
  let c : OrbitalIndex G theta → ℂ → ℂ :=
    fun i beta => (orbitalBasis G theta i).val (R+beta)
  let v : OrbitalIndex G theta → Core (OrbitalIndex G theta) ℂ :=
    fun i => modeAnnihilate (rawJetMode G theta j R) (annihilate i p)
  have hc (i) : Continuous (c i) :=
    (rawLLL_continuous G theta 1 (orbitalBasis G theta i)).comp
      (continuous_const.add continuous_id)
  have he (beta : ℂ) : modeAnnihilate (rawJetMode G theta j R)
      (modeAnnihilate (evaluationCoordinates G theta (R+beta)) p) = ∑ i, c i beta • v i := by
    rw [modeAnnihilate_evaluation_expansion]
    simp only [map_sum, map_smul, c, v]
  simpa only [he] using finite_combination_normSq_continuous c hc v

end TorusLean.Shared.ThermalCoherentSpectralDouble
