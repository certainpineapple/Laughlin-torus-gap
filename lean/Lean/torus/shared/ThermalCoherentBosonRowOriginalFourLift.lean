import torus.shared.ThermalCoherentBosonRowOriginalFour
import torus.shared.ThermalCoherentBosonRowIntegral
import torus.shared.BosonNatFourMatrixLift

/-! The independently defined original normal tensor, inserted through its
actual anchored N4 rank sources and the project's genuine full four-body lift.
All literal coefficients retain the annihilator orbital-factorial denominator.
This is a source identity and domain statement, not a relative certificate bound. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowOriginalFourLift
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.TwoBodyLift TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonNatFourAnnihilator TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Shared.ThermalCoherentFourBodyFrame
open TorusLean.Shared.ThermalCoherentFourBodyLift TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.ThermalCoherentBosonRowOriginalFour
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators
local instance originalFourLift_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private abbrev TensorIndex := Fin natFourOriginalTerms.length
private def tensorLeft (z : TensorIndex) : Core ℕ ℂ :=
  scaledWord factorialRootNat (natFourOriginalTerms.get z).creators
private def tensorRight (z : TensorIndex) : Core ℕ ℂ :=
  scaledWord factorialRootNat (natFourOriginalTerms.get z).annihilators
private def tensorCoefficient (z : TensorIndex) : ℂ :=
  ((natFourOriginalTerms.get z).coefficient:ℂ) /
    (natFourOrbitalMetric (natFourOriginalTerms.get z).annihilators:ℂ)
private theorem tensorLeft_particle (z : TensorIndex) : (tensorLeft z).IsHomogeneous 4 := by
  rw [tensorLeft,scaledWordNat_monomial]
  exact MvPolynomial.isHomogeneous_monomial _ ((wordOccupation_degree_nat _).trans
    (natFourOriginalTerms_shape _ (List.get_mem _ z)).1)
private theorem tensorRight_particle (z : TensorIndex) : (tensorRight z).IsHomogeneous 4 := by
  rw [tensorRight,scaledWordNat_monomial]
  exact MvPolynomial.isHomogeneous_monomial _ ((wordOccupation_degree_nat _).trans
    (natFourOriginalTerms_shape _ (List.get_mem _ z)).2.1)

/-- The original tensor coefficients inserted as actual anchored N4 dyads. -/
def originalM4SourceAt (G : Geometry) (theta : Twist) (R : ℂ) :
    FourSector (OrbitalIndex G theta) →ₗ[ℂ] FourSector (OrbitalIndex G theta) :=
  ∑ z : TensorIndex, tensorCoefficient z • fourSeedRankOne
    (natFourSeed G theta (tensorLeft z) (tensorLeft_particle z) 0 R)
    (natFourSeed G theta (tensorRight z) (tensorRight_particle z) 0 R)

private theorem finite_tensor_lift_inner {I : Type*} [Fintype I]
    (G : Geometry) (theta : Twist) (R : ℂ) (p q : I → Core ℕ ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 4) (hq : ∀ i, (q i).IsHomogeneous 4)
    (c : I → ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    ip f (fourBodyLift (∑ i, c i • fourSeedRankOne
      (natFourSeed G theta (p i) (hp i) 0 R)
      (natFourSeed G theta (q i) (hq i) 0 R)) g) =
      ∑ i, c i * ip (natFourAnnihilator G theta R (p i) f)
        (natFourAnnihilator G theta R (q i) g) := by
  have hrow (i : I) : ip f (fourBodyLift (fourSeedRankOne
      (natFourSeed G theta (p i) (hp i) 0 R)
      (natFourSeed G theta (q i) (hq i) 0 R)) g) =
      ip (natFourAnnihilator G theta R (p i) f)
        (natFourAnnihilator G theta R (q i) g) := by
    rw [fourBodyLift_rank_inner,natFourAnnihilator_ground G theta (p i) (hp i) R,
      natFourAnnihilator_ground G theta (q i) (hq i) R]
    rfl
  change ip f (fourBodyLiftLinear (∑ i, c i • fourSeedRankOne
    (natFourSeed G theta (p i) (hp i) 0 R)
    (natFourSeed G theta (q i) (hq i) 0 R)) g) = _
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    inner_sum_right,TwoBodyLift.inner_smul_right]
  change (∑ i, c i * ip f (fourBodyLift (fourSeedRankOne
    (natFourSeed G theta (p i) (hp i) 0 R)
    (natFourSeed G theta (q i) (hq i) 0 R)) g)) = _
  simp only [hrow]

private theorem list_index_sum {α : Type*} (L : List α) (B : α → ℂ) :
    (∑ i : Fin L.length, B (L.get i)) = (L.map B).sum := by
  rw [←List.sum_ofFn]
  congr 1
  simpa only [Function.comp_def] using
    (List.map_ofFn (f := L.get) (g := B)).symm.trans (congrArg (List.map B) (List.ofFn_get L))

private theorem literal_tensor_lift_inner (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ip f (fourBodyLift (originalM4SourceAt G theta R) g) = originalM4TensorCross G theta R f g := by
  rw [originalM4SourceAt,finite_tensor_lift_inner G theta R tensorLeft tensorRight
    tensorLeft_particle tensorRight_particle tensorCoefficient f g]
  exact list_index_sum natFourOriginalTerms (fun term =>
    (term.coefficient:ℂ)/(natFourOrbitalMetric term.annihilators:ℂ) *
      ip (natFourAnnihilator G theta R (scaledWord factorialRootNat term.creators) f)
        (natFourAnnihilator G theta R (scaledWord factorialRootNat term.annihilators) g))

/-- The original raw K4 equals the actual full-L4 image of that same literal
source, on every finite physical core and in both complex cross slots. -/
theorem actualRows_four_original_L4_cross (G : Geometry) (theta : Twist) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ ρ : RowIndex, actualRowFourCross G theta ρ R f g) =
      ip f (fourBodyLift (originalM4SourceAt G theta R) g) :=
  (actualRows_four_original_cross G theta R f g).trans (literal_tensor_lift_inner G theta R f g).symm

/-- Cell form of the original full-L4 source, with the original charge two. -/
def originalM4SourceCellForm (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, (ip f (fourBodyLift (originalM4SourceAt G theta R) f)).re ∂cellMeasure G 2

/-- The source-cell form has a true L1 domain and is exactly the raw K4 term
in the original K-square decomposition. -/
theorem actualRows_four_original_L4_integral (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => (ip f (fourBodyLift (originalM4SourceAt G theta R) f)).re)
      (cellMeasure G 2) ∧
    (∫ R, ∑ ρ : RowIndex, (actualRowFourCross G theta ρ R f f).re ∂cellMeasure G 2) =
      originalM4SourceCellForm G theta f := by
  have he (R : ℂ) : (∑ ρ : RowIndex, (actualRowFourCross G theta ρ R f f).re) =
      (ip f (fourBodyLift (originalM4SourceAt G theta R) f)).re := by
    simpa only [Complex.re_sum] using congrArg Complex.re (actualRows_four_original_L4_cross G theta R f f)
  constructor
  · exact (integrable_finsetSum Finset.univ
      (fun ρ _ => actualRowFourCross_real_integrable G theta ρ f)).congr
        (Filter.Eventually.of_forall he)
  · exact integral_congr_ae (Filter.Eventually.of_forall he)

end TorusLean.Shared.ThermalCoherentBosonRowOriginalFourLift
