import torus.shared.PhysicalBosonSingleAnchoredSeries
import torus.shared.BosonThermalJacobiTail

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonSingleTailPayment
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeRemovalTrace TorusLean.Shared.BosonThermalJacobiRows
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentAnchoredCOMSummability
open TorusLean.Shared.PhysicalBosonSingleAnchoredSeries TorusLean.Shared.BosonThermalJacobiTail
open TorusLean.Fermion.LatticePacking
open scoped BigOperators
local instance singleTail_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem anchoredRelativeCross_self_re (G : Geometry) (theta : Twist) (d : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (anchoredRelativeCross G theta d f f).re = w3RelativeForm G theta d f := by
  have hi := natThreeRemoval_cross_integrable G theta 3 (w3RelativeSeed d) (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1 0 0 f f
  unfold anchoredRelativeCross w3RelativeForm
  have hr := integral_re hi
  change (∫ R, (ip (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 0 R f) (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 0 R f)).re ∂cellMeasure G 3) =
    (∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 0 R f) (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 0 R f) ∂cellMeasure G 3).re at hr
  rw [←hr]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  exact occupationInner_self_re (fun _ => 1) _

def originalSingleForm (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  (ip f (TorusLean.Shared.BosonLiftSquare.contractionLift
    (TorusLean.Boson.PhysicalContactLiftCandidate.contactPairCoordinates G theta)
    TorusLean.Shared.BosonPairContractions.singleContraction f)).re

theorem originalSingleForm_relative_hasSum (G : Geometry) (theta : Twist)
    (hG : 20 ≤ systole G) (N : ℕ) (f : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) :
    HasSum (fun d => 2*(-1/2:ℝ)^d*w3RelativeForm G theta d f)
      (originalSingleForm G theta f) := by
  have hs := (anchoredCOM_relative_hasSum G theta f f hG).summable.hasSum
  rw [←original_singleContraction_relative_series G theta hG N N f f hf hf] at hs
  have hr := Complex.hasSum_re hs
  simpa only [originalSingleForm,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,anchoredRelativeCross_self_re] using hr

private theorem low_term_le_with_tail (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) (d : ℕ) :
    (if d ∈ Finset.range 9 then 2*(-1/2:ℝ)^d*w3RelativeForm G theta d f else 0) ≤
      2*(-1/2:ℝ)^d*w3RelativeForm G theta d f + oddRelativeTailTerm G theta f d := by
  have hq := w3RelativeForm_nonneg G theta d f
  by_cases hd : d<9
  · rw [if_pos (Finset.mem_range.mpr hd)]
    have hz : oddRelativeTailTerm G theta f d = 0 := by
      unfold oddRelativeTailTerm
      exact if_neg (by omega)
    rw [hz,add_zero]
  · have h9 : 9≤d := by omega
    rw [if_neg (fun h => hd (Finset.mem_range.mp h))]
    unfold oddRelativeTailTerm
    rcases Nat.even_or_odd d with he|ho
    · rw [if_neg (fun h => (Nat.not_odd_iff_even.mpr he) h.1),
        show (-1/2:ℝ)=-(1/2:ℝ) by ring,he.neg_pow]
      positivity
    · rw [if_pos ⟨ho,h9⟩,show (-1/2:ℝ)=-(1/2:ℝ) by ring,ho.neg_pow]
      linarith

/-- The high odd correction in the original S3 is paid by the already
proved physical tail; the entire low relative spectrum is retained. -/
theorem originalSingleForm_low_minus_tail (G : Geometry) (theta : Twist)
    (hG : 20 ≤ systole G) (N : ℕ) (f : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N+3)) :
    (∑ d ∈ Finset.range 9, 2*(-1/2:ℝ)^d*w3RelativeForm G theta d f) -
      (∑' d, oddRelativeTailTerm G theta f d) ≤ originalSingleForm G theta f := by
  have hs := originalSingleForm_relative_hasSum G theta hG N f hf
  have ht := (oddRelativeTail_bound G theta f hG).1
  have hl : HasSum (fun d => if d ∈ Finset.range 9 then
      2*(-1/2:ℝ)^d*w3RelativeForm G theta d f else 0)
      (∑ d ∈ Finset.range 9, 2*(-1/2:ℝ)^d*w3RelativeForm G theta d f) := by
    have h : HasSum (fun d => if d ∈ Finset.range 9 then
        2*(-1/2:ℝ)^d*w3RelativeForm G theta d f else 0)
        (∑ d ∈ Finset.range 9, if d ∈ Finset.range 9 then
        2*(-1/2:ℝ)^d*w3RelativeForm G theta d f else 0) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.range 9)
      (f := fun d => if d ∈ Finset.range 9 then
        2*(-1/2:ℝ)^d*w3RelativeForm G theta d f else 0)
      (fun d hd => if_neg hd)
    simpa only [Finset.sum_extend_by_zero] using h
  have h := hasSum_le (low_term_le_with_tail G theta f) hl (hs.add ht.hasSum)
  linarith

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonLinearEquiv TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.BosonSystole20Scalar

/-- The original high odd S3 tail has the same original-H / S4 payment on
every complete physical sector N+4. No particle-number factor survives. -/
theorem actual_originalSingleForm_low_payment (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hG : 20≤systole G) :
    (∑ d ∈ Finset.range 9, 2*(-1/2:ℝ)^d*w3RelativeForm G theta d
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val) -
      (30*(5/9:ℝ)^9)*sAllowance *
        (cAllowance * actualPositiveFourBodyForm G theta N f +
          actualParticleContactEnergy G ((N+2)+2) f.val) ≤
    originalSingleForm G theta ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val := by
  have hp : (((physicalSectorEquiv G theta ((N+2)+2)).symm f).val).IsHomogeneous ((N+1)+3) := by
    simpa only [Nat.add_assoc,show (2+2:ℕ)=1+3 by decide] using
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp
        ((physicalSectorEquiv G theta ((N+2)+2)).symm f).property
  have hs := originalSingleForm_low_minus_tail G theta hG (N+1)
    ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val hp
  have ht := actual_oddRelativeTail_bound G theta N f hG
  linarith

end TorusLean.Shared.PhysicalBosonSingleTailPayment
