import torus.shared.BosonAnchoredCoordinateRows
import torus.shared.BosonAnchoredKRows
import torus.shared.PhysicalBosonSingleExterior

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open TorusLean.Boson.SpectatorControl
namespace TorusLean.Shared.BosonAnchoredCoordinateCross
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.BosonAnchoredScalarExpansion
open TorusLean.Shared.BosonAnchoredCoordinateRows TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.ThermalCoherentJacobiInsertion TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Shared.BosonThermalJacobiRows
open scoped BigOperators ComplexConjugate
local instance coordinateCross_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Exact finite assembly of the three exterior torus orbitals into the
actual ket and bra removal rows. No integral or convergence is assumed. -/
theorem anchored_coordinate_cross (G : Geometry) (theta : Twist) (R : ℂ) (l : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (natThreeAnnihilator G theta R (w3Seed l) f)
      (natThreeAnnihilator G theta R (pairAnchoredSeed l) g) =
    ∑ i : OrbitalIndex G theta, ∑ a : PairIndex (OrbitalIndex G theta),
      ip (annihilate i (modePair (evaluationCoordinates G theta R) f))
        (modeAnnihilate (evaluationCoordinates G theta R) (pairRemove a g)) *
      conj (rawJetCoefficient G theta (orbitalBasis G theta i) l R) *
      pairJetCoefficient G theta (orbitalBasis G theta a.1)
        (orbitalBasis G theta a.2) R l := by
  rw [w3Annihilator_eq_original,LinearMap.comp_apply,
    rawJetMode_annihilate_expansion,pairAnchoredSeed_coordinate_expansion]
  simp only [TwoBodyLift.inner_sum_left,TwoBodyLift.inner_sum_right,
    TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,Complex.star_def,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  ring

end TorusLean.Shared.BosonAnchoredCoordinateCross
