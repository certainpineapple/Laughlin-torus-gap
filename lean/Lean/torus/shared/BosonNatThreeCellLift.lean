import torus.shared.BosonNatThreeCOMColumnTransport
import torus.shared.BosonNatThreeMatrixLift

/-! The full original three-body lift of a finite Nat source density,
integrated at an explicit cell charge. Source transfer uses charge two;
relative-vacuum transfer uses charge three. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeCellLift
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonNatThreeMatrixLift
open TorusLean.Shared.BosonNatThreeAnnihilator
open MeasureTheory Matrix
open scoped BigOperators
local instance cellLift_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def natMatrixCellLiftForm (G : Geometry) (theta : Twist) (k : ℕ) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, (ip f (threeBodyLift
    (rankOneRealization (fun i => natThreeSeed G theta (p i) (hp i) 0 R) C) f)).re
      ∂cellMeasure G k

theorem natMatrixCellLiftForm_eq_annihilator (G : Geometry) (theta : Twist) (k : ℕ) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta k p hp C f =
      ∫ R, (∑ i, ∑ j, C i j * ip
        (natThreeAnnihilator G theta R (p i) f)
        (natThreeAnnihilator G theta R (p j) f)).re ∂cellMeasure G k := by
  simp only [natMatrixCellLiftForm,rankOneRealization_lift_inner,
    natThreeAnnihilator_ground G theta _ (hp _) ,natThreeRemoval]

theorem natMatrixCellLiftForm_charge_three (G : Geometry) (theta : Twist) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 3 p hp C f = natMatrixLiftForm G theta p hp C f := rfl

theorem natMatrixCellLiftForm_annihilator_integrable (G : Geometry) (theta : Twist)
    (k : ℕ) {r : ℕ} (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ∑ i, ∑ j, C i j * ip
      (natThreeAnnihilator G theta R (p i) f)
      (natThreeAnnihilator G theta R (p j) g)) (cellMeasure G k) := by
  simp_rw [natThreeAnnihilator_ground G theta _ (hp _)]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (natThreeRemoval_cross_integrable G theta k (p i) (p j)
    (hp i) (hp j) 0 0 f g).const_mul (C i j)

theorem natMatrixCellLiftForm_eq_integral_re (G : Geometry) (theta : Twist)
    (k : ℕ) {r : ℕ} (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta k p hp C f =
      (∫ R, ∑ i, ∑ j, C i j * ip
        (natThreeAnnihilator G theta R (p i) f)
        (natThreeAnnihilator G theta R (p j) f) ∂cellMeasure G k).re := by
  rw [natMatrixCellLiftForm_eq_annihilator]
  have h := integral_re (natMatrixCellLiftForm_annihilator_integrable G theta k p hp C f f)
  change (∫ R, (∑ i, ∑ j, C i j * ip
    (natThreeAnnihilator G theta R (p i) f)
    (natThreeAnnihilator G theta R (p j) f)).re ∂cellMeasure G k) =
    (∫ R, ∑ i, ∑ j, C i j * ip
    (natThreeAnnihilator G theta R (p i) f)
    (natThreeAnnihilator G theta R (p j) f) ∂cellMeasure G k).re at h
  exact h

end TorusLean.Shared.BosonNatThreeCellLift
