import torus.shared.ThermalCoherentJacobiInsertion
import torus.shared.ThermalCoherentInsertionThreeLift
import torus.shared.ThermalCoherentSpectralIntegral
import torus.shared.BosonPeriodizedSeedNat

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiLift
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl
open TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.BosonThreeBodyLift TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentInsertionAlgebra
open TorusLean.Shared.ThermalCoherentInsertionPhysical TorusLean.Shared.ThermalCoherentInsertionThreeLift
open TorusLean.Shared.ThermalCoherentOccupation TorusLean.Shared.ThermalCoherentSpectralOccupation
open TorusLean.Shared.ThermalCoherentSpectralIntegral
open scoped TensorProduct

local instance jacobiPhysicalOrbital_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def physicalW3Seed (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    ThreeSector (PhysicalBosonSector.OrbitalIndex G theta) :=
  coherentThreeSector (evaluationCoordinates G theta R) (rawJetMode G theta j R)

/-- The source entering the Jacobi calculation is exactly the periodized
normalized pair-plus-spectator physical seed. -/
theorem physicalW3Seed_val (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    (physicalW3Seed G theta j R).val = anchoredSeedNat G theta R (w3Seed j) := by
  simp only [physicalW3Seed,coherentThreeSector,threeInsertion_tmul,fockSym2Map_symTensor,
    fockCoherentPair,modeCreate_apply,mul_one,w3Seed,pairVacuum,map_mul,map_smul,
    anchoredSeedNat_X,evaluationCoordinates_eq_rawJetCoordinates,rawJetMode,pow_two]

theorem physicalW3Seed_removal (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    threeSeedRemoval (physicalW3Seed G theta j R) =
      (modeAnnihilate (rawJetMode G theta j R)).comp (modePair (evaluationCoordinates G theta R)) :=
  threeSeedRemoval_coherent _ _

theorem anchored_w3Seed_adjoint (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ)
    (f p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    occupationInner (fun _ => 1) (anchoredSeedNat G theta R (w3Seed j)*f) p =
      occupationInner (fun _ => 1) f
        (modeAnnihilate (rawJetMode G theta j R) (modePair (evaluationCoordinates G theta R) p)) := by
  rw [← physicalW3Seed_val]
  exact threeInsertion_coherent_adjoint _ _ f p

/-- The already accepted all-N spectral row is the original generic L3
rank-one form of this actual Jacobi source, with no particle-number premise. -/
theorem physicalW3Seed_lift_form (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    (occupationInner (fun _ => 1) p
      (threeBodyLift (threeSeedRankOne (physicalW3Seed G theta j R)) p)).re =
      anchoredJetNormSq G theta p j R := by
  rw [physicalW3Seed,threeBodyLift_coherent_rankOne,coherentThreeLift_inner]
  rfl

end TorusLean.Shared.BosonThermalJacobiLift
