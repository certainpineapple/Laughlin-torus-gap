import torus.shared.BosonNatFourPairProduct
import torus.shared.BosonFiniteCertificateNatFourS4RelativeSeed
import torus.shared.BosonRelativeFrameAllN

/-! The original S4 relative source has exactly the already bounded physical
fourBodyJet image. Source binomial coefficients, both pair normalizations,
and the charge-four cell measure are retained. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourS4Physical
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonNatFourPairProduct
open TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.PhysicalBosonS4Positive
open TorusLean.Shared.PhysicalBosonS4Coefficients TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open MeasureTheory
open scoped BigOperators ComplexConjugate
local instance s4Physical_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem natFourAnnihilator_pair_relative_seed (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R (natFourPairRelativeSeed d) f =
      fourBodyJet G theta d R f := by
  simp only [natFourPairRelativeSeed,map_sum,LinearMap.sum_apply,
    LinearMap.map_smulₛₗ,LinearMap.smul_apply,starRingEnd_apply,
    natFourAnnihilator_pair_product,
    fourBodyJet,LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro p hp
  change conj (relativeBinomialCoeff d p) •
    pairDescendant G theta (d-p) R (pairDescendant G theta p R f) = _
  rw [relativeBinomialCoeff_conj]
  exact congrArg (fun z => relativeBinomialCoeff d p • z)
    (pairDescendant_commute G theta (d-p) p R R f)

theorem natFourAnnihilator_s4_relative (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R (w4RelativeSeed 0 d) f =
      fourBodyJet G theta d R f := by
  rw [←natFourPairRelativeSeed_eq_marked]
  exact natFourAnnihilator_pair_relative_seed G theta d R f

theorem actual_s4_relative_cutoff_budget (G : Geometry) (theta : Twist)
    (M D : ℕ) (hD : D≤16) (hG : 20≤systole G)
    (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous M) :
    (∫ R, ∑ d : Fin (D+1), occupationMetricNormSq (fun _ => 1)
      (natFourAnnihilator G theta R (w4RelativeSeed 0 d.val) f)
      ∂cellMeasure G 4) ≤
      (1+allowance)*(normalOrderedFourBodyForm G theta f).re := by
  simp_rw [natFourAnnihilator_s4_relative]
  exact coreFourJetEnergy_le_S4 G theta M D hD hG f hf

#print axioms natFourAnnihilator_pair_relative_seed
#print axioms natFourAnnihilator_s4_relative
#print axioms actual_s4_relative_cutoff_budget
end TorusLean.Shared.BosonNatFourS4Physical
