import torus.shared.BosonAnchoredPairRows
import torus.shared.BosonAnchoredScalarExpansion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredCoordinateRows
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.BosonAnchoredScalarExpansion
open TorusLean.Shared.BosonAnchoredPairRows TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonPairCOMCoefficientBound TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.ThermalCoherentOccupation
open scoped BigOperators ComplexConjugate
local instance coordinateRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem rawJetMode_annihilate_expansion (G : Geometry) (theta : Twist) (R : ℂ)
    (j : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    modeAnnihilate (rawJetMode G theta j R) f =
      ∑ i, rawJetCoefficient G theta (orbitalBasis G theta i) j R • annihilate i f := by
  have hi (i : OrbitalIndex G theta) : star (rawJetMode G theta j R i) =
      rawJetCoefficient G theta (orbitalBasis G theta i) j R := by
    simp only [rawJetMode,OrthonormalBasis.repr_apply_apply,Complex.star_def,
      inner_conj_symm,rawPlaneJet_inner_reproduces]
  simp only [modeAnnihilate,LinearMap.sum_apply,LinearMap.smul_apply,hi]

/-- The ordered physical pair basis carries precisely its old sqrt2
normalization, also for two different moving modes. -/
theorem mode_double_pair_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (u v : Orbital ι) (f : Core ι ℂ) :
    modeAnnihilate v (modeAnnihilate u f) = (Real.sqrt (2:ℝ):ℂ) •
      ∑ a : PairIndex ι, (star (u a.1) * star (v a.2)) • pairRemove a f := by
  have h2 : (Real.sqrt (2:ℝ):ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt (2:ℝ) ≠ 0 by positivity)
  have hm (w : Orbital ι) (q : Core ι ℂ) :
      modeAnnihilate w q = ∑ i, star (w i) • annihilate i q := by
    simp only [modeAnnihilate,LinearMap.sum_apply,LinearMap.smul_apply]
  rw [hm,hm]
  simp only [map_sum,map_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  simp only [Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hp : pairRemove (i,j) f = (Real.sqrt (2:ℝ):ℂ)⁻¹ •
      annihilate j (annihilate i f) := by
    simp only [pairRemove,LinearMap.smul_apply,LinearMap.comp_apply]
  rw [hp,smul_smul]
  congr 1
  field_simp [h2]
  <;> ring

theorem pairAnchoredSeed_coordinate_expansion (G : Geometry) (theta : Twist) (R : ℂ)
    (l : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    natThreeAnnihilator G theta R (pairAnchoredSeed l) f =
      ∑ a : PairIndex (OrbitalIndex G theta),
        pairJetCoefficient G theta (orbitalBasis G theta a.1) (orbitalBasis G theta a.2) R l •
          modeAnnihilate (evaluationCoordinates G theta R) (pairRemove a f) := by
  have hj (j : ℕ) (i : OrbitalIndex G theta) : star (rawJetMode G theta j R i) =
      rawJetCoefficient G theta (orbitalBasis G theta i) j R := by
    simp only [rawJetMode,OrthonormalBasis.repr_apply_apply,Complex.star_def,
      inner_conj_symm,rawPlaneJet_inner_reproduces]
  rw [pairAnchoredSeed_row_expansion]
  simp_rw [mode_double_pair_expansion]
  simp only [map_smul,map_sum,Finset.smul_sum,smul_smul,hj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [pairJetCoefficient,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show rawJetMode G theta 0 R = evaluationCoordinates G theta R from
    (evaluationCoordinates_eq_rawJetCoordinates G theta R).symm]
  congr 1
  ring

end TorusLean.Shared.BosonAnchoredCoordinateRows
