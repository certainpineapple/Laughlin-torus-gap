import torus.shared.BosonThreeBodyLiftContraction

/-! Genuine two-cell integration of the original bosonic CCR contraction
coefficients. The one-edge unfolding and anchored planar identity are separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonContractionIntegral
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.TwoBodyLift TorusLean.Boson.PhysicalContactLiftCandidate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonDiagonal
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.BosonLiftSquare
open TorusLean.Shared.BosonPairContractions
open scoped BigOperators ComplexConjugate
local instance contractionIntegral_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

def coefficientKernel (G : Geometry) (theta : Twist)
    (a b : PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) (R : ℂ) : ℂ :=
  conj (pairProduct G theta a.1 a.2 R) * pairProduct G theta b.1 b.2 R

lemma coefficientKernel_continuous (G : Geometry) (theta : Twist)
    (a b : PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) : Continuous (coefficientKernel G theta a b) :=
  (Complex.continuous_conj.comp (pairProduct_continuous G theta a.1 a.2)).mul
    (pairProduct_continuous G theta b.1 b.2)

lemma coefficientKernel_integrable (G : Geometry) (theta : Twist)
    (a b : PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :
    Integrable (coefficientKernel G theta a b) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2 (coefficientKernel_continuous G theta a b)

lemma coefficientKernel_integral (G : Geometry) (theta : Twist)
    (a b : PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :
    (∫ R, coefficientKernel G theta a b R ∂cellMeasure G 2) =
      pairKernel (contactPairCoordinates G theta) a b := by
  rw [contactPairKernel_actual]
  rfl

def twoCenterExpansion (G : Geometry) (theta : Twist)
    (T : PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) →
      PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → ℂ)
    (R S : ℂ) : ℂ :=
  ∑ p, ∑ q, ∑ r, ∑ s,
    (coefficientKernel G theta p q R * coefficientKernel G theta r s S) * T p q r s

lemma twoCenterExpansion_integrable (G : Geometry) (theta : Twist)
    (T : PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) →
      PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → ℂ) :
    Integrable (fun z : ℂ × ℂ => twoCenterExpansion G theta T z.1 z.2)
      ((cellMeasure G 2).prod (cellMeasure G 2)) := by
  unfold twoCenterExpansion
  exact integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_prod
        (coefficientKernel_integrable G theta r s)).mul_const _))))

lemma twoCenterExpansion_slice_integrable (G : Geometry) (theta : Twist)
    (T : PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) →
      PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → ℂ) (R : ℂ) :
    Integrable (twoCenterExpansion G theta T R) (cellMeasure G 2) := by
  apply continuous_integrable_cellMeasure G 2
  unfold twoCenterExpansion
  exact continuous_finsetSum _ (fun p _ => continuous_finsetSum _ (fun q _ =>
    continuous_finsetSum _ (fun r _ => continuous_finsetSum _ (fun s _ =>
      ((coefficientKernel_continuous G theta r s).const_mul _).mul_const _))))

lemma twoCenterExpansion_inner_integral (G : Geometry) (theta : Twist)
    (T : PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) →
      PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → ℂ) (R : ℂ) :
    (∫ S, twoCenterExpansion G theta T R S ∂cellMeasure G 2) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (coefficientKernel G theta p q R * pairKernel (contactPairCoordinates G theta) r s) * T p q r s := by
  unfold twoCenterExpansion
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const, integral_const_mul]
  rw [coefficientKernel_integral]

/-- Fubini-compatible genuine double-cell coefficient calculation. -/
theorem twoCenterExpansion_integral (G : Geometry) (theta : Twist)
    (T : PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) →
      PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → ℂ) :
    (∫ R, ∫ S, twoCenterExpansion G theta T R S ∂cellMeasure G 2 ∂cellMeasure G 2) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (pairKernel (contactPairCoordinates G theta) p q * pairKernel (contactPairCoordinates G theta) r s) * T p q r s := by
  simp_rw [twoCenterExpansion_inner_integral]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const, integral_mul_const]
  rw [coefficientKernel_integral]

/-- Original normalized contraction operator, integrated entry by entry on
its unchanged finite occupation carrier. K can be the actual single or double
CCR contraction; no target kernel identity is an input. -/
theorem contractionLift_double_integral (G : Geometry) (theta : Twist)
    (K : PairIndex (PhysicalBosonSector.OrbitalIndex G theta) → PairIndex (PhysicalBosonSector.OrbitalIndex G theta) →
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ] Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    ip f (contractionLift (contactPairCoordinates G theta) K g) =
      ∫ R, ∫ S, twoCenterExpansion G theta
        (fun a b c d => ip (pairRemove a f) (K b c (pairRemove d g))) R S
        ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  rw [twoCenterExpansion_integral]
  simp only [contractionLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, inner_sum_right, TwoBodyLift.inner_smul_right,
    pairCreate_remove_adjoint]

theorem singleContraction_double_integral (G : Geometry) (theta : Twist)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    ip f (contractionLift (contactPairCoordinates G theta) singleContraction g) =
      ∫ R, ∫ S, twoCenterExpansion G theta
        (fun a b c d => ip (pairRemove a f) (singleContraction b c (pairRemove d g))) R S
        ∂cellMeasure G 2 ∂cellMeasure G 2 :=
  contractionLift_double_integral G theta singleContraction f g

end TorusLean.Shared.PhysicalBosonContractionIntegral
