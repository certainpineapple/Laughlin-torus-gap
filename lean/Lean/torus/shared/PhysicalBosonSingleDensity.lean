import torus.shared.PhysicalBosonContractionModeSum
import torus.shared.ThermalCoherentOccupation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonSingleDensity
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonDiagonal
open TorusLean.Shared.PhysicalBosonContractionIntegral
open TorusLean.Shared.PhysicalBosonContractionModes
open TorusLean.Shared.BosonPairContractions TorusLean.Shared.BosonLiftSquare
open TorusLean.Boson.PhysicalContactLiftCandidate
open scoped BigOperators ComplexConjugate
local instance singleDensity_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def singleDensity (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R S : ℂ) : ℂ :=
  (2*inner ℂ (evaluationCoordinates G theta R) (evaluationCoordinates G theta S)) *
    ip (modeAnnihilate (evaluationCoordinates G theta S)
      (modePair (evaluationCoordinates G theta R) f))
      (modeAnnihilate (evaluationCoordinates G theta R)
        (modePair (evaluationCoordinates G theta S) g))

/-- The actual four CCR single contractions combine with the original two
normalized pair factors. The Gram is the full raw nonorthogonal Gram. -/
theorem singleDensity_eq_coefficients (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R S : ℂ) :
    singleDensity G theta f g R S = twoCenterExpansion G theta
      (fun a b c d => ip (pairRemove a f) (singleContraction b c (pairRemove d g))) R S := by
  have heval (T : ℂ) (i : PhysicalBosonSector.OrbitalIndex G theta) :
      evaluationCoordinates G theta T i = conj ((orbitalBasis G theta i).val T) := by
    simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ)
      (evaluationCoordinates_conj G theta T i)
  rw [singleDensity,mode_annihilate_adjoint,←TwoBodyLift.inner_smul_right,
    ←singleContraction_mode_sum]
  simp only [modePair_evaluation_expansion,map_sum,map_smul,
    inner_sum_left,inner_sum_right,TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,
    Finset.mul_sum,twoCenterExpansion,coefficientKernel]
  conv_lhs => arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp only [Complex.star_def,heval,pairProduct,map_mul,Complex.conj_conj]
  ring

theorem singleDensity_joint_integrable (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun z : ℂ × ℂ => singleDensity G theta f g z.1 z.2)
      ((cellMeasure G 2).prod (cellMeasure G 2)) := by
  simp_rw [singleDensity_eq_coefficients]
  exact twoCenterExpansion_integrable G theta _

theorem original_singleContraction_integral (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    ip f (contractionLift (contactPairCoordinates G theta) singleContraction g) =
      ∫ R, ∫ S, singleDensity G theta f g R S ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  simp_rw [singleDensity_eq_coefficients]
  exact singleContraction_double_integral G theta f g

end TorusLean.Shared.PhysicalBosonSingleDensity
