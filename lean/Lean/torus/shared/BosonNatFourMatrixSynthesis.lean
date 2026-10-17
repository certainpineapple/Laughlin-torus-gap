import torus.shared.BosonNatFourMatrixCOMTrace
import torus.shared.BosonNatFourRankCongruence
import torus.shared.BosonFiniteCertificateNatRelativeRankComparisonCore

/-! A true source dyad is transported through the original full-L4 cell form.
No orthogonality of the periodized source family is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourMatrixSynthesis
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourAnnihilator TorusLean.Shared.BosonNatFourRankCongruence
open MeasureTheory
open scoped BigOperators
local instance matrixSynthesis_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Both synthesis coefficients are retained with their actual conjugation;
the equality is with the original physical cell integral. -/
theorem natFourMatrixCellLiftForm_synthesized_rank {r : ℕ}
    (G : Geometry) (theta : Twist) (k : ℕ) (w : Fin r → Core ℕ ℂ)
    (hw : ∀ i, (w i).IsHomogeneous 4) (x : Fin r → ℂ) (γ : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta k w hw
      (Matrix.of fun i j => γ*(x i*star (x j))) f =
      ∫ R, (γ * ip
        (natFourAnnihilator G theta R (natFamilySynthesis w x) f)
        (natFourAnnihilator G theta R (natFamilySynthesis w x) f)).re
        ∂cellMeasure G k := by
  rw [natFourMatrixCellLiftForm_eq_annihilator]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  dsimp only [Matrix.of_apply]
  have h := fourSeedCombination_cross G theta R w (fun i (_ : Fin 1) => x i) 0 0 f f
  change ip (natFourAnnihilator G theta R (natFamilySynthesis w x) f)
    (natFourAnnihilator G theta R (natFamilySynthesis w x) f) = _ at h
  rw [h]
  simp only [Finset.mul_sum,mul_assoc]

#print axioms natFourMatrixCellLiftForm_synthesized_rank
end TorusLean.Shared.BosonNatFourMatrixSynthesis
