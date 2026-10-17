import torus.shared.ThermalCoherentJacobiFourInsertion
import torus.shared.ThermalCoherentInsertionFourLift
import torus.shared.ThermalCoherentSpectralDoubleIntegral
import torus.shared.BosonPeriodizedSeedNat

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiFourLift
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl
open TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.ThermalCoherentFourBodyFrame TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.ThermalCoherentJacobiInsertion TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentInsertionAlgebra
open TorusLean.Shared.ThermalCoherentInsertionPhysical TorusLean.Shared.ThermalCoherentInsertionFourLift
open TorusLean.Shared.ThermalCoherentOccupation TorusLean.Shared.ThermalCoherentSpectralOccupation
open TorusLean.Shared.ThermalCoherentSpectralDouble
open scoped TensorProduct

local instance fourJacobiPhysical_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def physicalW4Seed (G : Geometry) (theta : Twist) (j m : ℕ) (R : ℂ) :
    FourSector (PhysicalBosonSector.OrbitalIndex G theta) :=
  coherentFourSector (evaluationCoordinates G theta R)
    (rawJetMode G theta j R) (rawJetMode G theta m R)

theorem physicalW4Seed_val (G : Geometry) (theta : Twist) (j m : ℕ) (R : ℂ) :
    (physicalW4Seed G theta j m R).val = anchoredSeedNat G theta R (w4Seed j m) := by
  simp only [physicalW4Seed,coherentFourSector,fourInsertion_tmul,fockSym2Map_symTensor,
    fockCoherentPair,modeCreate_apply,mul_one,w4Seed,pairVacuum,spectatorSymScalar,map_mul,map_smul,
    anchoredSeedNat_X,evaluationCoordinates_eq_rawJetCoordinates,rawJetMode,pow_two]
  simp only [mul_smul_comm,smul_mul_assoc,mul_assoc]

theorem physicalW4Seed_removal (G : Geometry) (theta : Twist) (j m : ℕ) (R : ℂ) :
    fourSeedRemoval (physicalW4Seed G theta j m R) =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        (spectatorPair (rawJetMode G theta j R) (rawJetMode G theta m R)).comp
          (modePair (evaluationCoordinates G theta R)) := fourSeedRemoval_coherent _ _ _

theorem anchored_w4Seed_adjoint (G : Geometry) (theta : Twist) (j m : ℕ) (R : ℂ)
    (f p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    occupationInner (fun _ => 1) (anchoredSeedNat G theta R (w4Seed j m)*f) p =
      occupationInner (fun _ => 1) f
        (normalizedDoubleRemoval (evaluationCoordinates G theta R)
          (rawJetMode G theta j R) (rawJetMode G theta m R) p) := by
  rw [← physicalW4Seed_val]
  exact fourInsertion_coherent_adjoint _ _ _ f p

theorem physicalW4Seed_lift_form (G : Geometry) (theta : Twist) (j m : ℕ) (R : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    (occupationInner (fun _ => 1) p
      (fourBodyLift (fourSeedRankOne (physicalW4Seed G theta j m R)
        (physicalW4Seed G theta j m R)) p)).re =
      (1/2:ℝ) * anchoredDoubleJetNormSq G theta p (j,m) R := by
  rw [physicalW4Seed,fourBodyLift_coherent_rankOne,coherentFourLift_inner]
  rfl
end TorusLean.Shared.BosonThermalJacobiFourLift
