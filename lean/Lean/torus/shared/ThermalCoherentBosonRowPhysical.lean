import torus.shared.ThermalCoherentBosonRowCCR
import torus.shared.ThermalCoherentBosonRowMetric
import torus.shared.ThermalCoherentBosonRowPairEnergy
import torus.shared.ThermalCoherentBosonRowDecode
import torus.shared.ThermalCoherentSpectralOccupation

/-! The literal decoded 138 rows instantiated in the actual raw torus jets.
This is the original finite polynomial core; no row is fitted to a desired
normal-order formula. Identification of the canonical source coefficients
with the separately constructed M3/M4 matrices is a further theorem. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open MeasureTheory TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.ThermalCoherentSpectralOccupation
open TorusLean.Shared.ThermalCoherentBosonRowCCR TorusLean.Shared.ThermalCoherentBosonRowMetric
open TorusLean.Shared.ThermalCoherentBosonRowPairEnergy
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open scoped BigOperators
local instance rowPhysical_nonempty (G : Geometry) (theta : Twist) : Nonempty (OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def entryJetFin (ρ : RowIndex) (a : EntryIndex ρ) : Fin 9 :=
  ⟨entryJet ρ a,Nat.lt_succ_of_le (entry_support ρ a).2.2.2.2.2⟩

def actualRowPair (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ) :=
  (rowLambda ρ:ℂ) • pairDescendant G theta ρ.1.val R

def actualRowAuxiliary (G : Geometry) (theta : Twist) (ρ : RowIndex) (a : EntryIndex ρ) (R : ℂ) :=
  (singleJetAnnihilator G theta (entryPair ρ a).2 R).comp
    (pairDescendant G theta (entryPair ρ a).1 R)

def actualRowGrouped (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ) (i : Fin 9) :=
  ∑ a ∈ Finset.univ.filter (fun a => entryJetFin ρ a=i),
    (rowAlpha ρ a:ℂ) • actualRowAuxiliary G theta ρ a R

def actualRow (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) : Core (OrbitalIndex G theta) ℂ :=
  actualRowPair G theta ρ R f + ∑ a : EntryIndex ρ,
    (rowAlpha ρ a:ℂ) • modeCreate (rawJetMode G theta (entryJet ρ a) R)
      (actualRowAuxiliary G theta ρ a R f)

def actualRowThreeCross (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℂ :=
  rowThreeCross (fun i : Fin 9 => rawJetMode G theta i.val R)
    (actualRowPair G theta ρ R) (actualRowGrouped G theta ρ R) f g

def actualRowFourCross (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℂ :=
  rowFourCross (fun i : Fin 9 => rawJetMode G theta i.val R)
    (actualRowGrouped G theta ρ R) f g

def actualRowMetricCross (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℂ :=
  rowMetricCross (fun i : Fin 9 => rawJetMode G theta i.val R)
    (actualRowGrouped G theta ρ R) f g

/-- Exact collection of all original columns by their created raw jet. -/
theorem actualRow_eq_grouped (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    actualRow G theta ρ R f = rowApply (fun i : Fin 9 => rawJetMode G theta i.val R)
      (actualRowPair G theta ρ R) (actualRowGrouped G theta ρ R) f := by
  symm
  exact rowApply_grouped _ _ (entryJetFin ρ) (fun a => (rowAlpha ρ a:ℂ))
    (fun a => actualRowAuxiliary G theta ρ a R) f

/-- Genuine raw-mode complex normal ordering of each literal row. -/
theorem actualRow_cross_normal_order (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (actualRow G theta ρ R f) (actualRow G theta ρ R g) =
      ip (actualRowPair G theta ρ R f) (actualRowPair G theta ρ R g) +
        actualRowThreeCross G theta ρ R f g + actualRowFourCross G theta ρ R f g +
          actualRowMetricCross G theta ρ R f g := by
  rw [actualRow_eq_grouped,actualRow_eq_grouped]
  exact rowApply_cross_normal_order _ _ _ f g

/-- Its diagonal is a true positive square, on every finite core. -/
theorem actualRow_normSq_nonneg (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) : 0≤q (actualRow G theta ρ R f) :=
  occupationMetricNormSq_nonneg _ _

/-- The only raw-mode error is paid by the actual common Gram allowance. -/
theorem actualRowMetric_bound (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (hG : 20≤systole G) (f : Core (OrbitalIndex G theta) ℂ) :
    ‖actualRowMetricCross G theta ρ R f f‖ ≤
      allowance*∑ i : Fin 9, q (actualRowGrouped G theta ρ R i f) := by
  unfold actualRowMetricCross rowMetricCross
  simp only [rawJetMode,LinearIsometryEquiv.inner_map_map]
  exact actual_jetGram_occupation_bound G theta 8 (by norm_num) R hG _

/-- Sharp coefficient-square payment after grouping, with no N factor. -/
theorem actualRowGrouped_bound (G : Geometry) (theta : Twist) (ρ : RowIndex) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∑ i : Fin 9, q (actualRowGrouped G theta ρ R i f)) ≤
      (∑ a : EntryIndex ρ, (rowAlpha ρ a)^2)*
        ∑ a : EntryIndex ρ, q (actualRowAuxiliary G theta ρ a R f) := by
  simp only [actualRowGrouped,LinearMap.sum_apply,LinearMap.smul_apply]
  exact grouped_output_norm_bound (entryJetFin ρ) (rowAlpha ρ)
    (fun a => actualRowAuxiliary G theta ρ a R f)

/-- The unchanged pair coefficient pays the unchanged physical H. -/
theorem actualRowPair_same_H (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, q (actualRowPair G theta ρ R f) ∂cellMeasure G 2) =
      (rowLambda ρ)^2*(ip f (contactCoreHamiltonian G theta f)).re := by
  simp only [actualRowPair,LinearMap.smul_apply,canonical_normSq_smul,
    Complex.normSq_ofReal]
  rw [integral_const_mul,pairDescendant_same_H_energy,pow_two]

end TorusLean.Shared.ThermalCoherentBosonRows
