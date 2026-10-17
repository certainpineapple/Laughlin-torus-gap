import torus.shared.ThermalCoherentBosonRowPhysical
import torus.shared.ThermalCoherentBosonRowAuxiliary

/-! The actual canonical three-body rank sources behind the decoded row CCR.
Their annihilation rows are proved equal to the raw-mode row expressions on
every finite core. Equality with the original certificate M3 restriction
still requires the independent canonical row-square source calculation. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.ThermalCoherentBosonRowCCR TorusLean.Shared.ThermalCoherentBosonRowAuxiliary
open TorusLean.Shared.BosonPairCOMCoefficientBound TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.ThermalCoherentSpectralOccupation
open MeasureTheory
open scoped BigOperators ComplexConjugate
local instance rowSource_nonempty (G : Geometry) (theta : Twist) : Nonempty (OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Original pair/spectator insertion is genuinely particle three. -/
theorem pairSpectator_source_sector (p j : ℕ) :
    (pairCOMSeed p*MvPolynomial.X j).IsHomogeneous 3 := by
  rw [pairCOMSeed_eq_coefficient_sum,Finset.sum_mul]
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 3).sum_mem
  intro i hi
  rw [smul_mul_assoc]
  apply Submodule.smul_mem
  exact ((MvPolynomial.isHomogeneous_X ℂ i).mul
    (MvPolynomial.isHomogeneous_X ℂ (p-i))).mul (MvPolynomial.isHomogeneous_X ℂ j)

def rowThreePairSeed (ρ : RowIndex) (i : Fin 9) : Core ℕ ℂ :=
  (rowLambda ρ:ℂ) • (pairCOMSeed ρ.1.val*MvPolynomial.X i.val)

def rowThreeAuxiliarySeed (ρ : RowIndex) (i : Fin 9) : Core ℕ ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a => entryJetFin ρ a=i),
    (rowAlpha ρ a:ℂ) • (pairCOMSeed (entryPair ρ a).1*MvPolynomial.X (entryPair ρ a).2)

theorem rowThreePairSeed_sector (ρ : RowIndex) (i : Fin 9) :
    (rowThreePairSeed ρ i).IsHomogeneous 3 :=
  (MvPolynomial.homogeneousSubmodule ℕ ℂ 3).smul_mem _ (pairSpectator_source_sector _ _)

theorem rowThreeAuxiliarySeed_sector (ρ : RowIndex) (i : Fin 9) :
    (rowThreeAuxiliarySeed ρ i).IsHomogeneous 3 := by
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 3).sum_mem
  intro a ha
  exact Submodule.smul_mem _ _ (pairSpectator_source_sector _ _)

/-- Empty high-degree creator fibers contribute zero, even though the unused
pair test source T_i can itself have degree above eight. -/
theorem rowThreeAuxiliarySeed_above_degree (ρ : RowIndex) (i : Fin 9)
    (hi : 8<ρ.1.val+i.val) : rowThreeAuxiliarySeed ρ i=0 := by
  unfold rowThreeAuxiliarySeed
  apply Finset.sum_eq_zero
  intro a ha
  have h := (Finset.mem_filter.mp ha).2
  have hv := congrArg Fin.val h
  change (entryPair ρ a).1+(entryPair ρ a).2-ρ.1.val=i.val at hv
  have hs := entry_support ρ a
  have hlo := hs.2.2.2.1
  have hhi := hs.2.2.2.2.1
  omega

/-- Exact all-core realization of the grouped source, including conjugate linearity. -/
theorem actualRowGrouped_eq_source (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (R : ℂ) (i : Fin 9) (f : Core (OrbitalIndex G theta) ℂ) :
    actualRowGrouped G theta ρ R i f =
      natThreeAnnihilator G theta R (rowThreeAuxiliarySeed ρ i) f := by
  simp only [actualRowGrouped,rowThreeAuxiliarySeed,map_sum,LinearMap.map_smulₛₗ,
    LinearMap.sum_apply,LinearMap.smul_apply,Complex.conj_ofReal,
    natThreeAnnihilator_pair_spectator,actualRowAuxiliary,LinearMap.comp_apply]

/-- The pair-row cross term is the same original source insertion. -/
theorem actualRowPair_annihilate_eq_source (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (R : ℂ) (i : Fin 9) (f : Core (OrbitalIndex G theta) ℂ) :
    modeAnnihilate (rawJetMode G theta i.val R) (actualRowPair G theta ρ R f) =
      natThreeAnnihilator G theta R (rowThreePairSeed ρ i) f := by
  simp only [rowThreePairSeed,LinearMap.map_smulₛₗ,LinearMap.smul_apply,
    Complex.conj_ofReal,natThreeAnnihilator_pair_spectator,
    actualRowPair,map_smul]
  rfl

/-- Genuine three-body source rows, before identifying their original M3 tensor. -/
theorem actualRowThreeCross_eq_source (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    actualRowThreeCross G theta ρ R f g =
      (∑ i : Fin 9, ip (natThreeAnnihilator G theta R (rowThreePairSeed ρ i) f)
        (natThreeAnnihilator G theta R (rowThreeAuxiliarySeed ρ i) g)) +
      (∑ i : Fin 9, ip (natThreeAnnihilator G theta R (rowThreeAuxiliarySeed ρ i) f)
        (natThreeAnnihilator G theta R (rowThreePairSeed ρ i) g)) +
      ∑ i : Fin 9, ip (natThreeAnnihilator G theta R (rowThreeAuxiliarySeed ρ i) f)
        (natThreeAnnihilator G theta R (rowThreeAuxiliarySeed ρ i) g) := by
  simp only [actualRowThreeCross,rowThreeCross,actualRowGrouped_eq_source,
    actualRowPair_annihilate_eq_source]

/-- Every source cross term has a real cell domain on every finite core. -/
theorem actualRowThreeCross_integrable (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => actualRowThreeCross G theta ρ R f g) (cellMeasure G 2) := by
  simp_rw [actualRowThreeCross_eq_source,
    natThreeAnnihilator_ground G theta _ (rowThreePairSeed_sector ρ _),
    natThreeAnnihilator_ground G theta _ (rowThreeAuxiliarySeed_sector ρ _)]
  exact ((integrable_finsetSum _ (fun i _ => natThreeRemoval_cross_integrable G theta 2 _ _
    (rowThreePairSeed_sector ρ i) (rowThreeAuxiliarySeed_sector ρ i) 0 0 f g)).add
    (integrable_finsetSum _ (fun i _ => natThreeRemoval_cross_integrable G theta 2 _ _
    (rowThreeAuxiliarySeed_sector ρ i) (rowThreePairSeed_sector ρ i) 0 0 f g))).add
    (integrable_finsetSum _ (fun i _ => natThreeRemoval_cross_integrable G theta 2 _ _
    (rowThreeAuxiliarySeed_sector ρ i) (rowThreeAuxiliarySeed_sector ρ i) 0 0 f g))

end TorusLean.Shared.ThermalCoherentBosonRows
