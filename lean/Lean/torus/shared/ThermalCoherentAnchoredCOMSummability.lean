import torus.shared.ThermalCoherentJacobiAnchoredWeights
import torus.shared.BosonThermalJacobiTransfer
import torus.shared.BosonOccupationCrossBound

/-! Absolute summation of the signed anchored COM coefficients against the
original charge-three relative cross forms. The absolute two-index series is
proved first using the genuine positive W3 heat series at a=2/3. Only after
that proof are signed COM sums and total-degree antidiagonals rearranged.
Both input cores are arbitrary finite polynomials, without a common-sector
hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentAnchoredCOMSummability
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonThermalJacobiTransfer
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Shared.ThermalCoherentIntegral
open TorusLean.Shared.BosonOccupationCrossBound
open scoped BigOperators ComplexConjugate

local instance anchoredCOM_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- The unchanged actual charge-three cell cross form. -/
def anchoredRelativeCross (G : Geometry) (theta : Twist) (d : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℂ :=
  ∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)
    (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R g)
      ∂cellMeasure G 3

private theorem relative_q_integrable (G : Geometry) (theta : Twist) (d : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => q (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 0 R f)) (cellMeasure G 3) := by
  have h := (natThreeRemoval_cross_integrable G theta 3 (w3RelativeSeed d) (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1 0 0 f f).re
  change Integrable (fun R => (ip (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 0 R f) (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 0 R f)).re) (cellMeasure G 3) at h
  simpa only [ip,q,occupationInner_self_re] using h

theorem anchoredRelativeCross_norm_le (G : Geometry) (theta : Twist) (d : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ‖anchoredRelativeCross G theta d f g‖ ≤
      (w3RelativeForm G theta d f+w3RelativeForm G theta d g)/2 := by
  have hi := natThreeRemoval_cross_integrable G theta 3 (w3RelativeSeed d) (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1 0 0 f g
  have hqf := relative_q_integrable G theta d f
  have hqg := relative_q_integrable G theta d g
  have hp (R : ℂ) :
      ‖ip (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)
        (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R g)‖ ≤
      (q (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)+
        q (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R g))/2 := by
    have hh := occupationInner_norm_young (fun _ => 1)
      (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R f)
      (natThreeRemoval G theta (w3RelativeSeed d) (w3RelativeSeed_bihomogeneous d).1 0 R g)
    change 2*‖ip _ _‖≤q _+q _ at hh
    linarith
  refine (norm_integral_le_integral_norm _).trans ?_
  have h := integral_mono hi.norm ((hqf.add hqg).div_const 2) hp
  simpa only [Pi.add_apply,integral_div,integral_add hqf hqg,w3RelativeForm] using h

private theorem half_heat_hasSum (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    HasSum (fun d => (1/2:ℝ)^(d+1)*w3RelativeForm G theta d f)
      (oneSpectatorForm G theta (2/3) f) := by
  have h := oneSpectatorForm_relative_hasSum G theta (2/3) (by norm_num) f hG
  norm_num only [show (2:ℝ)/(2+3*(2/3))=1/2 by norm_num] at h
  exact h

private theorem relative_weight_majorant (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (d : ℕ) :
    (2*(1/2:ℝ)^d)*‖anchoredRelativeCross G theta d f g‖ ≤
      2*((1/2:ℝ)^(d+1)*w3RelativeForm G theta d f+
        (1/2:ℝ)^(d+1)*w3RelativeForm G theta d g) := by
  have h := mul_le_mul_of_nonneg_left (anchoredRelativeCross_norm_le G theta d f g)
    (by positivity : 0≤2*(1/2:ℝ)^d)
  convert h using 1 <;> rw [pow_succ] <;> ring

private theorem relative_weight_summable (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    Summable (fun d => (2*(1/2:ℝ)^d)*‖anchoredRelativeCross G theta d f g‖) :=
  Summable.of_nonneg_of_le (fun d => by positivity)
    (relative_weight_majorant G theta f g)
    (((half_heat_hasSum G theta f hG).summable.add (half_heat_hasSum G theta g hG).summable).mul_left 2)

/-- Literal signed COM term, before either index is summed. -/
def anchoredCOMTerm (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (dn : ℕ×ℕ) : ℂ :=
  (anchoredJacobiCrossWeight dn.1 dn.2 : ℂ)*anchoredRelativeCross G theta dn.1 f g

private theorem norm_COM_term (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (d n : ℕ) :
    ‖anchoredCOMTerm G theta f g (d,n)‖ =
      ‖anchoredJacobiCrossWeight d n‖*‖anchoredRelativeCross G theta d f g‖ := by
  simp only [anchoredCOMTerm,norm_mul,Complex.norm_real,Real.norm_eq_abs]

/-- The complete ordered double series is absolutely summable before any
signed cancellation or antidiagonal rearrangement is invoked. -/
theorem anchoredCOM_summable_norm (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    Summable (fun dn : ℕ×ℕ => ‖anchoredCOMTerm G theta f g dn‖) := by
  apply (summable_prod_of_nonneg (fun dn => norm_nonneg _)).mpr
  constructor
  · intro d
    simpa only [norm_COM_term] using
      ((hasSum_norm_anchoredJacobiCrossWeight d).mul_right ‖anchoredRelativeCross G theta d f g‖).summable
  · have he (d : ℕ) : (∑' n, ‖anchoredCOMTerm G theta f g (d,n)‖) =
        (2*(1/2:ℝ)^d)*‖anchoredRelativeCross G theta d f g‖ := by
      simpa only [norm_COM_term] using
        ((hasSum_norm_anchoredJacobiCrossWeight d).mul_right ‖anchoredRelativeCross G theta d f g‖).tsum_eq
    simpa only [he] using relative_weight_summable G theta f g hG

theorem anchoredCOM_norm_tsum_le (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    (∑' dn : ℕ×ℕ, ‖anchoredCOMTerm G theta f g dn‖) ≤
      2*(oneSpectatorForm G theta (2/3) f+oneSpectatorForm G theta (2/3) g) := by
  have hs := anchoredCOM_summable_norm G theta f g hG
  have hf := hs.hasSum.prod_fiberwise (fun d =>
    by simpa only [norm_COM_term] using
      (hasSum_norm_anchoredJacobiCrossWeight d).mul_right ‖anchoredRelativeCross G theta d f g‖)
  rw [←hf.tsum_eq]
  have hh := ((half_heat_hasSum G theta f hG).add (half_heat_hasSum G theta g hG)).mul_left 2
  rw [←hh.tsum_eq]
  exact (relative_weight_summable G theta f g hG).tsum_le_tsum
    (relative_weight_majorant G theta f g) hh.summable

private theorem signed_COM_hasSum (C : ℕ → ℂ)
    (hs : Summable (fun dn : ℕ×ℕ => (anchoredJacobiCrossWeight dn.1 dn.2 : ℂ)*C dn.1)) :
    HasSum (fun d => ((2*(-1/2:ℝ)^d : ℝ) : ℂ)*C d)
      (∑' dn : ℕ×ℕ, (anchoredJacobiCrossWeight dn.1 dn.2 : ℂ)*C dn.1) := by
  have hn (d : ℕ) : HasSum (fun n => (anchoredJacobiCrossWeight d n : ℂ)*C d)
      (((2*(-1/2:ℝ)^d : ℝ) : ℂ)*C d) := by
    have hw : HasSum (fun n => (anchoredJacobiCrossWeight d n : ℂ))
        ((2*(-1/2:ℝ)^d : ℝ) : ℂ) :=
      Complex.hasSum_ofReal.mpr (hasSum_anchoredJacobiCrossWeight d)
    exact hw.mul_right (C d)
  exact HasSum.prod_fiberwise hs.hasSum hn

/-- Signed n-summation is now legitimate, after absolute product summability. -/
theorem anchoredCOM_relative_hasSum (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    HasSum (fun d => ((2*(-1/2:ℝ)^d : ℝ) : ℂ)*anchoredRelativeCross G theta d f g)
      (∑' dn : ℕ×ℕ, anchoredCOMTerm G theta f g dn) := by
  have hs : Summable (anchoredCOMTerm G theta f g) :=
    (anchoredCOM_summable_norm G theta f g hG).of_norm
  exact signed_COM_hasSum (fun d => anchoredRelativeCross G theta d f g) hs

/-- The original finite degree-l sums have exactly the same sum as the
relative signed series; every ordered (d,n) occurs once in l=d+n. -/
theorem anchoredCOM_antidiagonal_hasSum (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    HasSum (fun l => ∑ d ∈ Finset.range (l+1),
      (anchoredJacobiCrossWeight d (l-d) : ℂ)*anchoredRelativeCross G theta d f g)
      (∑' d, ((2*(-1/2:ℝ)^d : ℝ) : ℂ)*anchoredRelativeCross G theta d f g) := by
  have hs : Summable (anchoredCOMTerm G theta f g) :=
    (anchoredCOM_summable_norm G theta f g hG).of_norm
  have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum).sigma
    (fun l => hasSum_fintype (fun dn : ↥(Finset.antidiagonal l) =>
      anchoredCOMTerm G theta f g dn.val))
  have h' : HasSum (fun l => ∑ dn ∈ Finset.antidiagonal l, anchoredCOMTerm G theta f g dn)
      (∑' dn : ℕ×ℕ, anchoredCOMTerm G theta f g dn) := by
    apply HasSum.congr_fun h
    intro l
    exact (Finset.sum_coe_sort (Finset.antidiagonal l) (anchoredCOMTerm G theta f g)).symm
  rw [←(anchoredCOM_relative_hasSum G theta f g hG).tsum_eq] at h'
  simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,anchoredCOMTerm] using h' 

end TorusLean.Shared.ThermalCoherentAnchoredCOMSummability
