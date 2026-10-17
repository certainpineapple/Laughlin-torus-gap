import torus.shared.BosonNatThreeCOMColumnTransport
import torus.shared.BosonNatThreeCellLift

/-! Uniqueness of source rank coefficients with the true nonunit Gram.
This is used before transporting a source action through periodization. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeRankDensityExt
open TorusLean.Boson TorusLean.BosonFiniteCertificate Matrix
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeRankCongruence
open TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeCellLift
open MeasureTheory
open scoped BigOperators

theorem gram_sandwich_cancel {r : ℕ} (F J C D : Matrix (Fin r) (Fin r) ℂ)
    (hFJ : F*J=1) (hJF : J*F=1) (h : F*C*F=F*D*F) : C=D := by
  have hc (A : Matrix (Fin r) (Fin r) ℂ) : J*(F*A*F)*J=A := by
    calc
      _ = (J*F)*A*(F*J) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJF,hFJ]; simp only [Matrix.one_mul,Matrix.mul_one]
  calc
    C = J*(F*C*F)*J := (hc C).symm
    _ = J*(F*D*F)*J := by rw [h]
    _ = D := hc D

theorem natFamilyRankForm_coefficient_ext {r : ℕ} (w : Fin r → Core ℕ ℂ)
    (F J C D : Matrix (Fin r) (Fin r) ℂ)
    (hF : natFamilyGram w=F) (hFJ : F*J=1) (hJF : J*F=1)
    (h : ∀ x y, natFamilyRankForm w C (natFamilySynthesis w x) (natFamilySynthesis w y) =
      natFamilyRankForm w D (natFamilySynthesis w x) (natFamilySynthesis w y)) : C=D := by
  classical
  apply gram_sandwich_cancel F J C D hFJ hJF
  ext i j
  have hh := h (Pi.single i 1) (Pi.single j 1)
  rw [natFamilyRankForm_synthesis,natFamilyRankForm_synthesis,hF] at hh
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using hh

theorem natFamilyRankForm_synthesized_rank {r : ℕ} (w : Fin r → Core ℕ ℂ)
    (x : Fin r → ℂ) (f g : Core ℕ ℂ) :
    natFamilyRankForm w (Matrix.of fun i j => x i * star (x j)) f g =
      star (natOccupationInner (natFamilySynthesis w x) f) *
        natOccupationInner (natFamilySynthesis w x) g := by
  rw [natFamilyRankForm_eq_sum]
  simp only [Matrix.of_apply,natFamilySynthesis,natOccupationInner_sum_left,
    natOccupationInner_smul_left,star_sum,star_mul,star_star,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => star (natOccupationInner (w i) f) * x i *
    (star (x j) * natOccupationInner (w j) g))]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem natFamilyRankForm_coefficient_eq_rank {r : ℕ} (w : Fin r → Core ℕ ℂ)
    (F J C : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℂ)
    (hF : natFamilyGram w=F) (hFJ : F*J=1) (hJF : J*F=1)
    (h : ∀ u v, natFamilyRankForm w C (natFamilySynthesis w u) (natFamilySynthesis w v) =
      star (natOccupationInner (natFamilySynthesis w x) (natFamilySynthesis w u)) *
        natOccupationInner (natFamilySynthesis w x) (natFamilySynthesis w v)) :
    C = Matrix.of (fun i j => x i * star (x j)) := by
  apply natFamilyRankForm_coefficient_ext w F J C _ hF hFJ hJF
  intro u v
  rw [h,natFamilyRankForm_synthesized_rank]

/-- A source dyad is transported through the actual annihilator and full L3,
without requiring the periodized source family to be orthogonal. -/
theorem natMatrixCellLiftForm_synthesized_rank {r : ℕ}
    (G : Geometry) (theta : Twist) (k : ℕ) (w : Fin r → Core ℕ ℂ)
    (hw : ∀ i, (w i).IsHomogeneous 3) (x : Fin r → ℂ) (γ : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta k w hw (Matrix.of fun i j => γ*(x i*star (x j))) f =
      (∫ R, γ * ip
        (natThreeAnnihilator G theta R (natFamilySynthesis w x) f)
        (natThreeAnnihilator G theta R (natFamilySynthesis w x) f)
        ∂cellMeasure G k).re := by
  rw [natMatrixCellLiftForm_eq_integral_re]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro R
  dsimp only [Matrix.of_apply]
  have h := seedCombination_cross G theta R w (fun i (_ : Fin 1) => x i) 0 0 f f
  change ip (natThreeAnnihilator G theta R (natFamilySynthesis w x) f)
    (natThreeAnnihilator G theta R (natFamilySynthesis w x) f) = _ at h
  rw [h]
  simp only [Finset.mul_sum,mul_assoc]

end TorusLean.Shared.BosonNatThreeRankDensityExt
