import torus.shared.BosonNatThreeRankCongruence
import torus.shared.BosonNatThreeMatrixLift

/-! Actual L3 congruence for a finite change of Nat source columns. This uses
only linearity of the original anchored seed map, without a periodization
isometry or an orthonormal-family assumption. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeMatrixLiftCongruence
open TorusLean.Boson TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeRankCongruence
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonNatThreeMatrixLift
open MeasureTheory
open scoped BigOperators
local instance matrixLiftCongruence_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem seedCombination_particle {r s : ℕ} (p : Fin r → Core ℕ ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 3) (S : Matrix (Fin r) (Fin s) ℂ) (j : Fin s) :
    (seedCombination p S j).IsHomogeneous 3 := by
  change (∑ i, S i j • p i) ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ 3
  apply Submodule.sum_mem
  intro i hi
  exact (MvPolynomial.homogeneousSubmodule ℕ ℂ 3).smul_mem _
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hp i))

theorem natMatrixLiftForm_seedCombination {r s : ℕ} (G : Geometry) (theta : Twist)
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (S : Matrix (Fin r) (Fin s) ℂ) (C : Matrix (Fin s) (Fin s) ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixLiftForm G theta (seedCombination p S) (seedCombination_particle p hp S) C f =
      natMatrixLiftForm G theta p hp (S*C*S.conjTranspose) f := by
  rw [natMatrixLiftForm_eq_rows,natMatrixLiftForm_eq_rows]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  have h := seedCombination_matrix_cross G theta R p S C f f
  simp_rw [natThreeAnnihilator_ground G theta (seedCombination p S _)
    (seedCombination_particle p hp S _) R,
    natThreeAnnihilator_ground G theta (p _) (hp _) R] at h
  exact congrArg Complex.re h

end TorusLean.Shared.BosonNatThreeMatrixLiftCongruence
