import torus.shared.BosonNatFourS4Physical
import torus.shared.BosonThermalJacobiFourRows

/-! The finite sum of the actual relative S4 source forms has the already
proved same-normal-S4 frame budget. Each scalar density is genuinely integrable
before the finite sum is interchanged with the charge-four integral. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourRelativeSourceBudget
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatFourS4Physical
open TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Shared.BosonThermalJacobiFourRows
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.PhysicalBosonS4Positive
open TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
open MeasureTheory
open scoped BigOperators
local instance sourceBudget_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem w4RelativeForm_s4_cutoff_allM_bound (G : Geometry) (theta : Twist)
    (M D : ℕ) (hD : D≤16) (hG : 20≤systole G)
    (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous M) :
    (∑ d : Fin (D+1), w4RelativeForm G theta 0 d.val f) ≤
      sAllowance*(normalOrderedFourBodyForm G theta f).re := by
  have hi (d : Fin (D+1)) : Integrable (fun R => q
      (natFourRemoval G theta (w4RelativeSeed 0 d.val)
        (w4RelativeSeed_bihomogeneous 0 d.val).1 0 R f)) (cellMeasure G 4) := by
    have h := (natFourRemoval_cross_integrable G theta 4
      (w4RelativeSeed 0 d.val) (w4RelativeSeed 0 d.val)
      (w4RelativeSeed_bihomogeneous 0 d.val).1
      (w4RelativeSeed_bihomogeneous 0 d.val).1 0 0 f f).re
    change Integrable (fun R => (ip
      (natFourRemoval G theta (w4RelativeSeed 0 d.val)
        (w4RelativeSeed_bihomogeneous 0 d.val).1 0 R f)
      (natFourRemoval G theta (w4RelativeSeed 0 d.val)
        (w4RelativeSeed_bihomogeneous 0 d.val).1 0 R f)).re) (cellMeasure G 4) at h
    simpa only [ip,q,occupationInner_self_re] using h
  have hb := actual_s4_relative_cutoff_budget G theta M D hD hG f hf
  simp_rw [natFourAnnihilator_ground G theta _
    (w4RelativeSeed_bihomogeneous 0 _).1] at hb
  change (∫ R, ∑ d : Fin (D+1), q
    (natFourRemoval G theta (w4RelativeSeed 0 d.val)
      (w4RelativeSeed_bihomogeneous 0 d.val).1 0 R f) ∂cellMeasure G 4) ≤ _ at hb
  rw [integral_finset_sum _ (fun d _ => hi d)] at hb
  exact hb

#print axioms w4RelativeForm_s4_cutoff_allM_bound
end TorusLean.Shared.BosonNatFourRelativeSourceBudget
