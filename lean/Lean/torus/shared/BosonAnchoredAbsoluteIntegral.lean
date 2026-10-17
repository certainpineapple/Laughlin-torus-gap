import torus.shared.BosonAnchoredRowBounds
import torus.shared.BosonAnchoredKRows
import torus.shared.NatAnchoredThreeBudget
import torus.shared.ThermalCoherentAnchoredSeries

/-! Absolute outer-cell convergence of the original anchored-K row series.
Fixed particle numbers enter only the domination proof. Each term uses the
actual unaltered annihilation rows and the original charge-two cell measure.
Absolute L1 summability is established before the sum/integral exchange. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredAbsoluteIntegral
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonAnchoredKRows
open TorusLean.Shared.BosonAnchoredRowBounds TorusLean.Shared.BosonOccupationCrossBound
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate ENNReal
local instance absoluteRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def anchoredRowTerm (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (l : ℕ) (R : ℂ) : ℂ :=
  (anchoredKernelCoefficient l : ℂ) *
    ip (natThreeAnnihilator G theta R (w3Seed l) f)
      (natThreeAnnihilator G theta R (pairAnchoredSeed l) g)

/-- Every single term is already an integrable original physical row. -/
theorem anchoredRowTerm_integrable (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (l : ℕ) :
    Integrable (anchoredRowTerm G theta f g l) (cellMeasure G 2) := by
  unfold anchoredRowTerm
  simp_rw [natThreeAnnihilator_ground G theta (w3Seed l) (w3Seed_sector l),
    natThreeAnnihilator_ground G theta (pairAnchoredSeed l) (pairAnchoredSeed_bihomogeneous l).1]
  exact (natThreeRemoval_cross_integrable G theta 2 (w3Seed l) (pairAnchoredSeed l)
    (w3Seed_sector l) (pairAnchoredSeed_bihomogeneous l).1 0 0 f g).const_mul
      (anchoredKernelCoefficient l : ℂ)

/-- Explicit fixed-sector majorant constant, independent of center and l. -/
def anchoredRowMajorant (G : Geometry) (theta : Twist) (N M : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  2*(4096+gaussianConstant)^3 *
    (((N:ℝ)+3)^3*occupationMetricNormSq (fun _ => 1) f +
      ((M:ℝ)+3)^3*occupationMetricNormSq (fun _ => 1) g)

private theorem anchoredRowMajorant_nonneg (G : Geometry) (theta : Twist) (N M : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) : 0 ≤ anchoredRowMajorant G theta N M f g := by
  have hC : 0 ≤ 4096+gaussianConstant := by linarith [gaussianConstant_nonneg]
  have hf := occupationMetricNormSq_nonneg (fun _ => 1) f
  have hg := occupationMetricNormSq_nonneg (fun _ => 1) g
  unfold anchoredRowMajorant
  positivity

/-- Actual cross-row domination. The inputs may have different fixed particle numbers. -/
theorem anchoredRowTerm_norm_le (G : Geometry) (theta : Twist) (hG : 1 ≤ systole G)
    (N M : ℕ) (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) (hg : g.IsHomogeneous (M+3)) (l : ℕ) (R : ℂ) :
    ‖anchoredRowTerm G theta f g l R‖ ≤
      anchoredRowMajorant G theta N M f g * (((l:ℝ)+1)^5*natAnchoredThreeDecayReal l) := by
  have hC : 0 ≤ 4096+gaussianConstant := by linarith [gaussianConstant_nonneg]
  have hqf := occupationMetricNormSq_nonneg (fun _ => 1) f
  have hqg := occupationMetricNormSq_nonneg (fun _ => 1) g
  have hleft := w3_row_normSq_polynomial G theta hG R l N f hf
  have hright := pairAnchored_row_normSq_polynomial G theta hG R l M g hg
  have hpow : ((l:ℝ)+1)^3 ≤ ((l:ℝ)+1)^5 :=
    pow_le_pow_right₀ (by have hl : 0 ≤ (l:ℝ) := Nat.cast_nonneg l; linarith) (by decide)
  have hleft' : occupationMetricNormSq (fun _ => 1)
      (natThreeAnnihilator G theta R (w3Seed l) f) ≤
      (4096+gaussianConstant)^3*((N:ℝ)+3)^3*((l:ℝ)+1)^5*
        occupationMetricNormSq (fun _ => 1) f := hleft.trans (by gcongr)
  have hk : 0 ≤ anchoredKernelCoefficient l := by unfold anchoredKernelCoefficient; positivity
  rw [anchoredRowTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
  calc
    _ ≤ anchoredKernelCoefficient l *
        (occupationMetricNormSq (fun _ => 1) (natThreeAnnihilator G theta R (w3Seed l) f) +
          occupationMetricNormSq (fun _ => 1) (natThreeAnnihilator G theta R (pairAnchoredSeed l) g)) :=
      mul_le_mul_of_nonneg_left (occupationInner_norm_le_sum (fun _ => 1) _ _) hk
    _ ≤ anchoredKernelCoefficient l *
        ((4096+gaussianConstant)^3*((N:ℝ)+3)^3*((l:ℝ)+1)^5*
          occupationMetricNormSq (fun _ => 1) f +
         (4096+gaussianConstant)^3*((M:ℝ)+3)^3*((l:ℝ)+1)^5*
          occupationMetricNormSq (fun _ => 1) g) :=
      mul_le_mul_of_nonneg_left (add_le_add hleft' hright) hk
    _ = _ := by unfold anchoredKernelCoefficient anchoredRowMajorant natAnchoredThreeDecayReal; ring

/-- Absolute pointwise summability follows from the proven original-row majorant. -/
theorem anchoredRowTerm_summable_norm (G : Geometry) (theta : Twist) (hG : 1 ≤ systole G)
    (N M : ℕ) (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) (hg : g.IsHomogeneous (M+3)) (R : ℂ) :
    Summable (fun l => ‖anchoredRowTerm G theta f g l R‖) := by
  apply Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l =>
    anchoredRowTerm_norm_le G theta hG N M f g hf hg l R)
  exact (natAnchoredThreeDecay_polynomial_summable 5).mul_left (anchoredRowMajorant G theta N M f g)

/-- The sum of actual L1 norms on the original charge-two cell is finite.
The finite cell mass is retained, not replaced by a probability normalization. -/
theorem anchoredRowTerm_summable_integral_norm (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (N M : ℕ) (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) (hg : g.IsHomogeneous (M+3)) :
    Summable (fun l => ∫ R, ‖anchoredRowTerm G theta f g l R‖ ∂cellMeasure G 2) := by
  have hs := ((natAnchoredThreeDecay_polynomial_summable 5).mul_left
    (anchoredRowMajorant G theta N M f g)).mul_left ((cellMeasure G 2).real Set.univ)
  apply Summable.of_nonneg_of_le (fun l => integral_nonneg (fun R => norm_nonneg _)) _ hs
  intro l
  have h := integral_mono (anchoredRowTerm_integrable G theta f g l).norm
    (integrable_const (anchoredRowMajorant G theta N M f g *
      (((l:ℝ)+1)^5*natAnchoredThreeDecayReal l)))
    (fun R => anchoredRowTerm_norm_le G theta hG N M f g hf hg l R)
  simpa only [integral_const, smul_eq_mul] using h

/-- Genuine integrability of the actual pointwise infinite row sum, after absolute L1. -/
theorem anchoredRow_tsum_integrable (G : Geometry) (theta : Twist) (hG : 1 ≤ systole G)
    (N M : ℕ) (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) (hg : g.IsHomogeneous (M+3)) :
    Integrable (fun R => ∑' l, anchoredRowTerm G theta f g l R) (cellMeasure G 2) := by
  have hi := anchoredRowTerm_integrable G theta f g
  have hs := anchoredRowTerm_summable_integral_norm G theta hG N M f g hf hg
  have he (l : ℕ) : (∫⁻ R, ‖anchoredRowTerm G theta f g l R‖ₑ ∂cellMeasure G 2) =
      ‖∫ R, ‖anchoredRowTerm G theta f g l R‖ ∂cellMeasure G 2‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi l).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun R => norm_nonneg _))]
    simp only [coe_nnnorm]
  have ht : (∑' l, ∫⁻ R, ‖anchoredRowTerm G theta f g l R‖ₑ ∂cellMeasure G 2) ≠ ∞ := by
    rw [funext he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  refine ⟨(AEMeasurable.tsum (fun l => (hi l).aemeasurable)).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun R => enorm_tsum_le_tsum_enorm)) ?_
  rw [lintegral_tsum (fun l => (hi l).aestronglyMeasurable.enorm)]
  exact ht.lt_top

/-- The original anchored block integrals sum to the integral of the true row series.
No target S3 identity or integrability premise is supplied as input. -/
theorem anchoredBlockForm_hasSum_integral (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (N M : ℕ) (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) (hg : g.IsHomogeneous (M+3)) :
    HasSum (fun l => anchoredBlockForm G theta l f g)
      (∫ R, ∑' l, anchoredRowTerm G theta f g l R ∂cellMeasure G 2) := by
  simpa only [anchoredBlockForm, anchoredRowTerm] using
    hasSum_integral_of_summable_integral_norm (anchoredRowTerm_integrable G theta f g)
      (anchoredRowTerm_summable_integral_norm G theta hG N M f g hf hg)

#print axioms anchoredRowTerm_integrable
#print axioms anchoredRowTerm_norm_le
#print axioms anchoredRowTerm_summable_norm
#print axioms anchoredRowTerm_summable_integral_norm
#print axioms anchoredRow_tsum_integrable
#print axioms anchoredBlockForm_hasSum_integral
end TorusLean.Shared.BosonAnchoredAbsoluteIntegral
