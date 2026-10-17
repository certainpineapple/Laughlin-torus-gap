import torus.shared.BosonAnchoredTripleRows
import torus.shared.BosonPairCOMCoefficientBound
import torus.shared.ThermalCoherentJacobiAnchoredAlgebra

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredPairRows
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonAnchoredTripleRows
open TorusLean.Shared.BosonPairCOMCoefficientBound
open TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Shared.ThermalCoherentSpectralOccupation
open scoped BigOperators ComplexConjugate
local instance pairRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Literal all-core annihilation row of the second anchored column, with
its original finite pair-COM coefficients. Repeated labels are retained. -/
theorem pairAnchoredSeed_row_expansion (G : Geometry) (theta : Twist) (R : ℂ)
    (l : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    natThreeAnnihilator G theta R (pairAnchoredSeed l) f =
      ∑ i ∈ Finset.range (l+1), (pairCOMCoefficientReal l i : ℂ) •
        modeAnnihilate (rawJetMode G theta 0 R)
          (modeAnnihilate (rawJetMode G theta (l-i) R)
            (modeAnnihilate (rawJetMode G theta i R) f)) := by
  rw [pairAnchoredSeed,pairCOMSeed_eq_coefficient_sum,Finset.sum_mul]
  simp only [smul_mul_assoc,map_sum,LinearMap.map_smulₛₗ,
    LinearMap.sum_apply,LinearMap.smul_apply,starRingEnd_apply,
    natThreeAnnihilator_triple]
  simp only [Complex.star_def,Complex.conj_ofReal]

end TorusLean.Shared.BosonAnchoredPairRows
