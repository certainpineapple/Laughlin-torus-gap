import torus.shared.ThermalCoherentBosonRowRegularity
import torus.shared.ThermalCoherentBosonRowCost

/-! Honest integration of the original positive row square and its raw-metric
error. The raw three/four-body terms are still named by their actual CCR
expressions; their original source-matrix identifications are independent. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open MeasureTheory TorusLean.Geometry TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.ThermalCoherentBosonRowCCR TorusLean.Shared.ThermalCoherentBosonRowPairEnergy
open TorusLean.Shared.ThermalCoherentBosonRowEnvelope TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonLinearEquiv TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Fermion.LatticePacking
open scoped BigOperators
local instance rowIntegral_nonempty (G : Geometry) (theta : Twist) : Nonempty (OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private theorem actualRow_real_normal_order (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (R : ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    q (actualRow G theta ρ R f) = q (actualRowPair G theta ρ R f) +
      (actualRowThreeCross G theta ρ R f f).re + (actualRowFourCross G theta ρ R f f).re +
      (actualRowMetricCross G theta ρ R f f).re := by
  have h := congrArg Complex.re (actualRow_cross_normal_order G theta ρ R f f)
  simpa only [Complex.add_re,ip,occupationInner_self_re] using h

private theorem actualRowPair_norm_integrable (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => q (actualRowPair G theta ρ R f)) (cellMeasure G 2) := by
  simp only [actualRowPair,LinearMap.smul_apply,canonical_normSq_smul,Complex.normSq_ofReal]
  exact (pairDescendant_normSq_integrable G theta f ρ.1.val).const_mul _

/-- The actual zero-contraction term has a genuine cell domain. -/
theorem actualRowFourCross_real_integrable (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => (actualRowFourCross G theta ρ R f f).re) (cellMeasure G 2) := by
  have h := ((actualRow_normSq_integrable G theta ρ f).sub
    (actualRowPair_norm_integrable G theta ρ f)).sub
      ((actualRowThreeCross_integrable G theta ρ f f).re)
  apply (h.sub (actualRowMetricCross_integrable G theta ρ f f).re).congr
  exact Filter.Eventually.of_forall fun R => by
    have he := actualRow_real_normal_order G theta ρ R f
    change q (actualRow G theta ρ R f) - q (actualRowPair G theta ρ R f) -
      (actualRowThreeCross G theta ρ R f f).re -
      (actualRowMetricCross G theta ρ R f f).re =
      (actualRowFourCross G theta ρ R f f).re
    linarith

def actualKForm (G : Geometry) (theta : Twist) (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, ∑ ρ : RowIndex, q (actualRow G theta ρ R f) ∂cellMeasure G 2

def actualMetricForm (G : Geometry) (theta : Twist) (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, (∑ ρ : RowIndex, actualRowMetricCross G theta ρ R f f).re ∂cellMeasure G 2

/-- This positivity is the original sum of squares, with an honest L1 domain. -/
theorem actualKForm_nonneg (G : Geometry) (theta : Twist) (f : Core (OrbitalIndex G theta) ℂ) :
    0≤actualKForm G theta f :=
  integral_nonneg (fun R => Finset.sum_nonneg (fun ρ _ => actualRow_normSq_nonneg G theta ρ R f))

/-- Integrated actual CCR identity, retaining explicit source-identification boundaries. -/
theorem actualKForm_normal_order (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    actualKForm G theta f = eta*(ip f (contactCoreHamiltonian G theta f)).re +
      (∫ R, ∑ ρ : RowIndex, (actualRowThreeCross G theta ρ R f f).re ∂cellMeasure G 2) +
      (∫ R, ∑ ρ : RowIndex, (actualRowFourCross G theta ρ R f f).re ∂cellMeasure G 2) +
      actualMetricForm G theta f := by
  have hp := integrable_finsetSum Finset.univ (fun ρ _ => actualRowPair_norm_integrable G theta ρ f)
  have h3 := integrable_finsetSum Finset.univ (fun ρ _ => (actualRowThreeCross_integrable G theta ρ f f).re)
  have h4 := integrable_finsetSum Finset.univ (fun ρ _ => actualRowFourCross_real_integrable G theta ρ f)
  have hm := integrable_finsetSum Finset.univ (fun ρ _ => (actualRowMetricCross_integrable G theta ρ f f).re)
  change Integrable (fun R => ∑ ρ : RowIndex,
    (actualRowThreeCross G theta ρ R f f).re) (cellMeasure G 2) at h3
  change Integrable (fun R => ∑ ρ : RowIndex,
    (actualRowMetricCross G theta ρ R f f).re) (cellMeasure G 2) at hm
  unfold actualKForm actualMetricForm
  simp_rw [actualRow_real_normal_order,Finset.sum_add_distrib,Complex.re_sum]
  have hsplit4 := integral_add ((hp.add h3).add h4) hm
  have hsplit3 := integral_add (hp.add h3) h4
  have hsplit2 := integral_add hp h3
  simp only [Pi.add_apply] at hsplit4 hsplit3 hsplit2
  rw [hsplit4,hsplit3,hsplit2]
  congr 3
  rw [integral_finsetSum _ (fun ρ _ => actualRowPair_norm_integrable G theta ρ f)]
  simp only [actualRowPair_same_H]
  rw [←Finset.sum_mul,eta_exact]
  rfl

/-- Absolute metric integral paid by the true complete auxiliary envelope. -/
theorem actualMetricForm_bound (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    |actualMetricForm G theta f| ≤ allowance*rowCost*
      (∫ R, auxiliaryEnvelope G theta 8 f R ∂cellMeasure G 2) := by
  have hm := integrable_finsetSum Finset.univ (fun ρ _ => actualRowMetricCross_integrable G theta ρ f f)
  have hr := integral_re hm
  change (∫ R, (∑ ρ : RowIndex, actualRowMetricCross G theta ρ R f f).re ∂cellMeasure G 2) = _ at hr
  unfold actualMetricForm
  rw [hr]
  calc
    _ ≤ ‖∫ R, ∑ ρ : RowIndex, actualRowMetricCross G theta ρ R f f ∂cellMeasure G 2‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∫ R, ‖∑ ρ : RowIndex, actualRowMetricCross G theta ρ R f f‖ ∂cellMeasure G 2 :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ R, allowance*rowCost*auxiliaryEnvelope G theta 8 f R ∂cellMeasure G 2 :=
      integral_mono hm.norm ((auxiliaryEnvelope_integrable G theta 8 f).const_mul _)
        (fun R => actualRows_metric_pointwise G theta R hG f)
    _ = _ := integral_const_mul _ _

/-- Original same-H/S4 payment with the exact paper coefficient kappa*c3*s. -/
theorem actualMetricForm_physical_bound (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hG : 20≤systole G) :
    |actualMetricForm G theta ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val| ≤
      (kappaAllowance*c3*sAllowance)*
        (cAllowance*actualPositiveFourBodyForm G theta N f+
          actualParticleContactEnergy G ((N+2)+2) f.val) := by
  apply (actualMetricForm_bound G theta _ hG).trans
  have h := mul_le_mul_of_nonneg_left (actual_auxiliaryEnvelope_bound G theta N f hG)
    (by norm_num [allowance,rowCost] : (0:ℝ)≤allowance*rowCost)
  convert h using 1 <;> dsimp [kappaAllowance,c3] <;> ring

end TorusLean.Shared.ThermalCoherentBosonRows
