import torus.shared.BosonRelativeFrameEnergy
import torus.shared.RelativeJetFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonRelativeFrame
open MeasureTheory TorusLean.Boson
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open scoped TensorProduct

/-- Continuity in every spectator coordinate follows from the independent
joint-entire physical carrier, including arbitrary finite core coefficients. -/
theorem coreFunction_continuous (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Continuous (coreFunction G theta N p) := by
  obtain ⟨H,hH,hf⟩ := ((slices_iff_joint_and_boundary G theta N _).mp
    (coreFunction_has_slices G theta N p)).1
  have he : coreFunction G theta N p = fun z => configurationGaussian N z * H z := funext hf
  rw [he]
  apply Continuous.mul _ hH.continuous
  unfold configurationGaussian
  apply continuous_finsetProd
  intro a ha
  unfold TorusLean.Geometry.gaussianFactor
  fun_prop

theorem doublePairTensor_continuous (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Continuous (doublePairTensor G theta N p) := by
  unfold doublePairTensor
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact (coreFunction_continuous G theta N _).smul
    (continuous_const : Continuous (fun _ : Configuration N =>
      pairSection G theta a ⊗ₜ[ℂ] pairSection G theta b))

/-- The actual finite relative frame applied to the original literal double
pair section, with all physical spectator variables retained. -/
def actualRelativeFourBodyForm (G : Geometry) (theta : Twist) (N D : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) : ℝ :=
  ∫ z, ‖relativeJetTruncation G theta D (physicalDoublePairTensor G theta N f z)‖^2
    ∂sectorMeasure G N

theorem actualRelativeFourBody_integrable (G : Geometry) (theta : Twist) (N D : ℕ)
    (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    Integrable (fun z => ‖relativeJetTruncation G theta D
      (physicalDoublePairTensor G theta N f z)‖^2) (sectorMeasure G N) := by
  let p := ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val
  have hc : Continuous (physicalDoublePairTensor G theta N f) := doublePairTensor_continuous G theta N p
  have hj : Continuous (fun z => ‖relativeJetTruncation G theta D
      (physicalDoublePairTensor G theta N f z)‖^2) :=
    (((relativeJetTruncation G theta D).continuous.comp hc).norm).pow 2
  have hi := (doublePairTensor_normSq_integrable G theta N p).const_mul (1+allowance)
  apply hi.mono' hj.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact RelativeJetFrame.relativeJetTruncation_energy G theta D hD hL _

/-- The genuine relative-frame cost is paid by the same positive S4 term,
with no spectator-number factor or identity-operator payment. -/
theorem actualRelativeFourBody_le_S4 (G : Geometry) (theta : Twist) (N D : ℕ)
    (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    actualRelativeFourBodyForm G theta N D f ≤
      (1+allowance) * actualPositiveFourBodyForm G theta N f := by
  let p := ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val
  unfold actualRelativeFourBodyForm
  calc
    _ ≤ ∫ z, (1+allowance) * ‖physicalDoublePairTensor G theta N f z‖^2 ∂sectorMeasure G N :=
      integral_mono (actualRelativeFourBody_integrable G theta N D hD hL f)
        ((doublePairTensor_normSq_integrable G theta N p).const_mul (1+allowance))
        (fun z => RelativeJetFrame.relativeJetTruncation_energy G theta D hD hL _)
    _ = _ := by rw [integral_const_mul, physicalDoublePairTensor_integrated_normSq]

#print axioms coreFunction_continuous
#print axioms doublePairTensor_continuous
#print axioms actualRelativeFourBody_integrable
#print axioms actualRelativeFourBody_le_S4
end TorusLean.Shared.BosonRelativeFrame
