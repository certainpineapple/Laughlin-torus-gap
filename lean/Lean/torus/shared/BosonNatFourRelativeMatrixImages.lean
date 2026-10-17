import torus.shared.BosonNatFourMatrixSynthesis
import torus.shared.BosonNatFourMatrixLinearity
import torus.shared.BosonFiniteCertificateNatFourRelativeS4Synthesis
import torus.shared.BosonFiniteCertificateNatFourRelativeHSynthesis
import torus.shared.ThermalCoherentNatFourHamiltonianCutoff

/-! The original S/H matrices, with their inverse Gram factors, synthesize
the same actual sources already used by the physical frame and heat bounds. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourRelativeMatrixImages
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourMatrixSynthesis TorusLean.Shared.BosonNatFourMatrixLinearity
open TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonThermalJacobiFourRows
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Shared.ThermalCoherentJacobiFourCutoff
open MeasureTheory
open scoped BigOperators
local instance matrixImages_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private theorem synthesized_relative_form {r : ℕ} (G : Geometry) (theta : Twist)
    (w : Fin r → Core ℕ ℂ) (hw : ∀ i, (w i).IsHomogeneous 4)
    (x : Fin r → ℂ) (a b : ℕ) (hx : natFamilySynthesis w x=w4RelativeSeed a b)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta 4 w hw (Matrix.vecMulVec x (star x)) f =
      w4RelativeForm G theta a b f := by
  have h := natFourMatrixCellLiftForm_synthesized_rank G theta 4 w hw x 1 f
  simp only [one_mul,Matrix.vecMulVec,Pi.star_apply] at h ⊢
  rw [h,hx]
  simp_rw [natFourAnnihilator_ground G theta _ (w4RelativeSeed_bihomogeneous a b).1]
  simp only [w4RelativeForm,ip,q,occupationInner_self_re]

theorem natFourRelativeS4MatrixCell_eq_source (G : Geometry) (theta : Twist)
    (d : Fin 17) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta 4 (natFourRelativeColumn d)
      (fun a => (natFourRelativeColumn_bihomogeneous d a).1)
      (natFourRelativeS4RankCoefficient d) f = w4RelativeForm G theta 0 d.val f := by
  rw [natFourRelativeS4RankCoefficient_dyad]
  exact synthesized_relative_form G theta _ _ _ _ _
    (natFourRelativeS4DualCoordinates_synthesis d) f

theorem natFourRelativeHMatrixCell_eq_sources (G : Geometry) (theta : Twist)
    (d : Fin 17) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta 4 (natFourRelativeColumn d)
      (fun a => (natFourRelativeColumn_bihomogeneous d a).1)
      (natFourRelativeHRankCoefficient d) f =
      ∑ a : Fin (d.val+1), w4RelativeForm G theta a.val (d.val-a.val) f := by
  rw [natFourRelativeHRankCoefficient_dyads]
  have h := natFourMatrixCellLiftForm_sum_smul (Finset.univ : Finset (Fin (d.val+1)))
    G theta 4 (natFourRelativeColumn d)
    (fun a => (natFourRelativeColumn_bihomogeneous d a).1) (fun _ => (1:ℝ))
    (fun a => Matrix.vecMulVec (natFourRelativeHDualCoordinates d a)
      (star (natFourRelativeHDualCoordinates d a))) f
  simp only [Complex.ofReal_one,one_smul,one_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a ha
  exact synthesized_relative_form G theta _ _ _ _ _
    (natFourRelativeHDualCoordinates_synthesis d a) f

theorem natFourRelativeHMatrixCell_sum_eq_cutoff (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∑ d : Fin 17, natFourMatrixCellLiftForm G theta 4 (natFourRelativeColumn d)
      (fun a => (natFourRelativeColumn_bihomogeneous d a).1)
      (natFourRelativeHRankCoefficient d) f) = fourRelativeCutoffForm G theta 16 f := by
  simp_rw [natFourRelativeHMatrixCell_eq_sources]
  rw [fourRelativeCutoffForm,fourRelativeTriangle_sum_diagonal]
  have h (d : ℕ) := Fin.sum_univ_eq_sum_range
    (fun a : ℕ => w4RelativeForm G theta a (d-a) f) (d+1)
  simp_rw [h]
  exact Fin.sum_univ_eq_sum_range
    (fun d : ℕ => ∑ a ∈ Finset.range (d+1), w4RelativeForm G theta a (d-a) f) 17

#print axioms natFourRelativeS4MatrixCell_eq_source
#print axioms natFourRelativeHMatrixCell_eq_sources
#print axioms natFourRelativeHMatrixCell_sum_eq_cutoff
end TorusLean.Shared.BosonNatFourRelativeMatrixImages
