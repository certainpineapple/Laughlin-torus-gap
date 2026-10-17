import torus.shared.BosonNatFourRemovalTrace

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourLiftForm
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Shared.ThermalCoherentInsertionFourLift
open TorusLean.Shared.BosonNatFourRemovalTrace
open MeasureTheory

local instance natLiftForm_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Every genuine homogeneous-four source row form is the previously
constructed full-core L4 rank-one lift, with the original normalization. -/
theorem natFourRemoval_lift_inner (G : Geometry) (theta : Twist)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 4) (n : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    ip f (fourBodyLift (fourSeedRankOne (natFourSeed G theta p hp n R) (natFourSeed G theta p hp n R)) f) =
      ip (natFourRemoval G theta p hp n R f) (natFourRemoval G theta p hp n R f) := by
  rw [fourBodyLift_fourSeedRankOne_apply]
  calc
    _ = star (ip ((natFourSeed G theta p hp n R).val *
      fourSeedRemoval (natFourSeed G theta p hp n R) f) f) :=
        (occupationInner_conj_symm (fun _ => 1) _ _).symm
    _ = star (ip (fourSeedRemoval (natFourSeed G theta p hp n R) f)
      (fourSeedRemoval (natFourSeed G theta p hp n R) f)) := by
        rw [fourSeedRemoval_adjoint]
    _ = _ := occupationInner_conj_symm (fun _ => 1) _ _

theorem natFourRemoval_lift_normSq (G : Geometry) (theta : Twist)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 4) (n : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (ip f (fourBodyLift (fourSeedRankOne (natFourSeed G theta p hp n R) (natFourSeed G theta p hp n R)) f)).re =
      q (natFourRemoval G theta p hp n R f) := by
  rw [natFourRemoval_lift_inner]
  exact occupationInner_self_re (fun _ => 1) _

end TorusLean.Shared.BosonNatFourLiftForm
