import torus.shared.BosonNatThreeCellLift

/-! Linearity in genuine finite rank coefficients inside the full L3 cell form. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeCellLinearity
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeCellLift
open TorusLean.Shared.BosonNatThreeAnnihilator
open MeasureTheory Matrix
open scoped BigOperators

theorem natMatrixCellLiftForm_sub (G : Geometry) (theta : Twist) (k : ℕ)
    {r : ℕ} (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C D : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta k p hp (C-D) f =
      natMatrixCellLiftForm G theta k p hp C f -
      natMatrixCellLiftForm G theta k p hp D f := by
  simp_rw [natMatrixCellLiftForm_eq_integral_re]
  simp only [Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  rw [integral_sub (natMatrixCellLiftForm_annihilator_integrable G theta k p hp C f f)
    (natMatrixCellLiftForm_annihilator_integrable G theta k p hp D f f),Complex.sub_re]

end TorusLean.Shared.BosonNatThreeCellLinearity
