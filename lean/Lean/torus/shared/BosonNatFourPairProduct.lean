import torus.shared.ThermalCoherentBosonRowFourSource
import torus.shared.ThermalCoherentBosonRowAuxiliary

/-! Genuine normalized pair-product sources act by the original two pair
annihilators on every physical core. This is the source-to-physical bridge
needed for the independently defined planar S4, with no new half factor. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourPairProduct
open TorusLean.Boson
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonPairCOMCoefficientBound
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.ThermalCoherentBosonRowAuxiliary
open TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.ThermalCoherentSpectralOccupation
open scoped BigOperators ComplexConjugate
local instance pairProduct_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem natFourAnnihilator_pair_product (G : Geometry) (theta : Twist) (R : ℂ)
    (p q : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R (pairCOMSeed p * pairCOMSeed q) f =
      pairDescendant G theta q R (pairDescendant G theta p R f) := by
  have he : natFourAnnihilator G theta R (pairCOMSeed p * pairCOMSeed q) f =
      ∑ i ∈ Finset.range (q+1), (pairCOMCoefficientReal q i:ℂ) •
        singleJetAnnihilator G theta (q-i) R
          (singleJetAnnihilator G theta i R (pairDescendant G theta p R f)) := by
    rw [pairCOMSeed_eq_coefficient_sum q,Finset.mul_sum,map_sum,LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_smul_comm,←mul_assoc,LinearMap.map_smulₛₗ,LinearMap.smul_apply]
    change conj (pairCOMCoefficientReal q i:ℂ) •
      natFourAnnihilator G theta R ((pairCOMSeed p*MvPolynomial.X i)*MvPolynomial.X (q-i)) f = _
    rw [Complex.conj_ofReal,natFourAnnihilator_mul_spectator G theta R _
      (pairSpectator_source_sector p i) (q-i),natThreeAnnihilator_pair_spectator]
    rfl
  rw [he,pairDescendant_eq_raw G theta q R (pairDescendant G theta p R f),
    Finset.smul_sum]
  simp only [smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pairCOMCoefficient_eq_descendant q i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]

#print axioms natFourAnnihilator_pair_product
end TorusLean.Shared.BosonNatFourPairProduct
