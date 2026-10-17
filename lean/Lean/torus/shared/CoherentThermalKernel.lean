import torus.shared.CoherentJetExpansion
import torus.shared.CoherentThermalCrossIntegral

/-! True all-level thermal matrix elements on the full torus LLL.
The actual coherent displacement retains its magnetic phase until that
unit-modulus phase cancels in the rank-one cross form. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.CoherentThermalKernel
open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetGramBounds
open TorusLean.Shared.CoherentJetExpansion TorusLean.Shared.CoherentThermalSummability
open TorusLean.Shared.CoherentThermalCrossIntegral TorusLean.Shared.ThermalCoherentGaussian
open TorusLean.Shared.ThermalCoherentMoments
open scoped ComplexConjugate

theorem coherentJetWeight_eq_conj_planeJet (beta : ℂ) (j : ℕ) :
    coherentJetWeight beta j = conj (planeJet j beta) := by
  have hg : conj (gaussianFactor 1 beta) = gaussianFactor 1 beta := by
    rw [gaussianFactor_eq_norm, ← Complex.exp_conj, Complex.conj_ofReal]
  simp only [coherentJetWeight, planeJet, map_div₀, map_mul, map_pow, hg, Complex.conj_ofReal]

private theorem scalar_cross_hasSum (w A B : ℕ → ℂ) (c x y : ℂ)
    (hA : HasSum (fun j => w j * A j) (c*x))
    (hB : HasSum (fun j => w j * B j) (c*y)) (hc : conj c*c=1) :
    HasSum (fun jm : ℕ × ℕ => conj (w jm.1) * w jm.2 * conj (A jm.1) * B jm.2)
      (conj x*y) := by
  have hs : HasSum (fun j => conj (w j * A j)) (conj (c*x)) :=
    Complex.hasSum_conj'.mpr hA
  have hnA : Summable (fun j : ℕ => ‖conj (w j * A j)‖) := hs.summable.norm
  have hnB : Summable (fun j : ℕ => ‖w j * B j‖) := hB.summable.norm
  have ht : Summable (fun jm : ℕ × ℕ => conj (w jm.1 * A jm.1) * (w jm.2 * B jm.2)) :=
    summable_mul_of_summable_norm (f := fun j : ℕ => conj (w j * A j))
      (g := fun j : ℕ => w j * B j) hnA hnB
  have hp := hs.mul hB ht
  have he : conj (c*x)*(c*y)=conj x*y := by
    rw [map_mul]
    calc
      _ = (conj c*c)*(conj x*y) := by ring
      _ = _ := by rw [hc, one_mul]
  rw [he] at hp
  apply hp.congr_fun
  intro jm
  simp only [map_mul]
  ring

theorem coherent_cross_hasSum (G : Geometry) (theta : Twist) (a : ℝ)
    (h k : LLL G theta 1) (R beta : ℂ) :
    HasSum (fun jm : ℕ × ℕ => thermalCrossTerm a
      (fun j => inner ℂ h (rawPlaneJet G theta j R))
      (fun j => inner ℂ k (rawPlaneJet G theta j R)) jm beta)
      ((thermalWeight a beta : ℂ) * conj (inner ℂ h (rawPlaneJet G theta 0 (R+beta))) *
        inner ℂ k (rawPlaneJet G theta 0 (R+beta))) := by
  have hphase : conj (magneticCocycle 1 R beta) * magneticCocycle 1 R beta = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      magneticCocycle_norm_one]
    norm_num
  have hp := (scalar_cross_hasSum (coherentJetWeight beta)
    (fun j => inner ℂ h (rawPlaneJet G theta j R))
    (fun j => inner ℂ k (rawPlaneJet G theta j R)) (magneticCocycle 1 R beta)
    (inner ℂ h (rawPlaneJet G theta 0 (R+beta)))
    (inner ℂ k (rawPlaneJet G theta 0 (R+beta)))
    (coherentJet_inner_hasSum G theta h R beta)
    (coherentJet_inner_hasSum G theta k R beta) hphase).mul_left (thermalWeight a beta : ℂ)
  have he : (thermalWeight a beta : ℂ) *
      (conj (inner ℂ h (rawPlaneJet G theta 0 (R+beta))) *
        inner ℂ k (rawPlaneJet G theta 0 (R+beta))) =
      (thermalWeight a beta : ℂ) * conj (inner ℂ h (rawPlaneJet G theta 0 (R+beta))) *
        inner ℂ k (rawPlaneJet G theta 0 (R+beta)) := (mul_assoc _ _ _).symm
  rw [he] at hp
  apply hp.congr_fun
  intro jm
  simp only [thermalCrossTerm, coherentJetWeight_eq_conj_planeJet, Complex.conj_conj]
  ring

/-- The actual coherent cross form is genuinely integrable on the whole
plane. Its domination uses the uniform physical ground-jet norm bound. -/
theorem actual_coherent_cross_integrable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ TorusLean.Fermion.LatticePacking.systole G)
    (a : ℝ) (ha : 0 < a) (h k : LLL G theta 1) (R : ℂ) :
    Integrable (fun beta => (thermalWeight a beta : ℂ) *
      conj (inner ℂ h (rawPlaneJet G theta 0 (R+beta))) *
      inner ℂ k (rawPlaneJet G theta 0 (R+beta))) planeMeasure := by
  let C : ℝ := 4096 + TorusLean.Fermion.LatticePacking.gaussianConstant
  have hj : Continuous (fun beta => rawPlaneJet G theta 0 (R+beta)) :=
    (PlaneJetParameterContinuity.rawPlaneJet_continuous G theta 0).comp
      (continuous_const.add continuous_id)
  have hc : Continuous (fun beta => (thermalWeight a beta : ℂ) *
      conj (inner ℂ h (rawPlaneJet G theta 0 (R+beta))) *
      inner ℂ k (rawPlaneJet G theta 0 (R+beta))) := by
    have hw := thermalWeight_continuous a
    fun_prop
  apply ((thermalWeight_integrable a ha).mul_const (‖h‖ * ‖k‖ * C)).mono'
    hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro beta
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thermalWeight_pos a beta), Complex.norm_conj]
  have hb : ‖rawPlaneJet G theta 0 (R+beta)‖^2 ≤ C := by
    simpa [C] using rawPlaneJet_norm_sq_le G theta hG 0 (R+beta)
  calc
    _ ≤ thermalWeight a beta * (‖h‖ * ‖rawPlaneJet G theta 0 (R+beta)‖) *
        (‖k‖ * ‖rawPlaneJet G theta 0 (R+beta)‖) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_inner_le_norm h _) (thermalWeight_pos a beta).le)
        (norm_inner_le_norm k _) (norm_nonneg _)
        (mul_nonneg (thermalWeight_pos a beta).le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = thermalWeight a beta * (‖h‖ * ‖k‖ * ‖rawPlaneJet G theta 0 (R+beta)‖^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (thermalWeight_pos a beta).le

/-- Infinite thermal diagonalization for every pair of genuine physical LLL
states. Its hypotheses contain neither a series/interchange budget nor a
thermal operator identity; both are proved from the actual torus jets. -/
theorem actual_coherent_thermal_hasSum (G : Geometry) (theta : Twist)
    (hG : 1 ≤ TorusLean.Fermion.LatticePacking.systole G)
    (a : ℝ) (ha : 0 < a) (h k : LLL G theta 1) (R : ℂ) :
    HasSum (fun j : ℕ => (thermalEigenvalue a j : ℂ) *
      conj (inner ℂ h (rawPlaneJet G theta j R)) * inner ℂ k (rawPlaneJet G theta j R))
      (∫ beta, (thermalWeight a beta : ℂ) *
        conj (inner ℂ h (rawPlaneJet G theta 0 (R+beta))) *
        inner ℂ k (rawPlaneJet G theta 0 (R+beta)) ∂planeMeasure) := by
  let A : ℕ → ℂ := fun j => inner ℂ h (rawPlaneJet G theta j R)
  let B : ℕ → ℂ := fun j => inner ℂ k (rawPlaneJet G theta j R)
  have hi := thermalCrossTerm_integral_hasSum a ha A B
    (weighted_rawPlaneJet_pairing_summable G theta hG a ha R h)
    (weighted_rawPlaneJet_pairing_summable G theta hG a ha R k)
  have he (beta : ℂ) : (∑' jm : ℕ × ℕ, thermalCrossTerm a A B jm beta) =
      (thermalWeight a beta : ℂ) * conj (inner ℂ h (rawPlaneJet G theta 0 (R+beta))) *
        inner ℂ k (rawPlaneJet G theta 0 (R+beta)) :=
    (coherent_cross_hasSum G theta a h k R beta).tsum_eq
  simp_rw [he] at hi
  apply HasSum.prod_fiberwise hi
  intro j
  have hf := hasSum_ite_eq j ((thermalEigenvalue a j : ℂ) * conj (A j) * B j)
  convert hf using 1
  ext m
  rw [thermalCrossTerm_integral a ha]
  by_cases hm : j=m
  · subst m; simp
  · simp [hm, Ne.symm hm]

end TorusLean.Shared.CoherentThermalKernel
