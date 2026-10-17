import torus.shared.BosonNatFourMatrixLinearity

/-! Congruence-correct finite source inequalities pass through the same
actual four-body lift. The matrix positivity premise is explicit here. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourMatrixComparison
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourMatrixLinearity
open scoped BigOperators ComplexOrder

/-- A genuine PSD comparison of the full coefficient matrices gives the
same inequality of their actual cell-integrated four-body lifts. -/
theorem natFourMatrixCellLiftForm_compare (G : Geometry) (theta : Twist)
    (charge : ℕ) {r : ℕ} (p : Fin r → Core ℕ ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 4)
    (C S H : Matrix (Fin r) (Fin r) ℂ) (α δ : ℝ)
    (hPSD : ((α:ℂ) • S + (δ:ℂ) • H - C).PosSemidef)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta charge p hp C f ≤
      α * natFourMatrixCellLiftForm G theta charge p hp S f +
      δ * natFourMatrixCellLiftForm G theta charge p hp H f := by
  have hl := natFourMatrixCellLiftForm_sum_smul (Finset.univ : Finset (Fin 2))
    G theta charge p hp ![α,δ] ![S,H] f
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hl
  have hn := natFourMatrixCellLiftForm_nonneg G theta charge p hp
    ((α:ℂ) • S + (δ:ℂ) • H - C) hPSD f
  rw [natFourMatrixCellLiftForm_sub,hl] at hn
  exact sub_nonneg.mp hn

#print axioms natFourMatrixCellLiftForm_compare
end TorusLean.Shared.BosonNatFourMatrixComparison
