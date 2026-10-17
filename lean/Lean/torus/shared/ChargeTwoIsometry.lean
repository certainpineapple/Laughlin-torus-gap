import torus.shared.ChargeTwoScaling

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.ChargeTwoIsometry

open MeasureTheory TorusLean.Shared.ChargeTwoScaling

def dilation : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero scale scale_pos.ne'

theorem dilation_apply (z : ℂ) : dilation z = (scale : ℂ) * z := by
  simp [dilation, Complex.real_smul]

theorem scaled_cell (G : Geometry) : cell (scaledGeometry G) = dilation '' cell G := by
  ext w
  constructor
  · intro hw
    obtain ⟨a,b,ha,ha',hb,hb',hw⟩ := (mem_cell_iff (scaledGeometry G) w).mp hw
    refine ⟨(a : ℂ)*G.omega1 + (b : ℂ)*G.omega2,
      (mem_cell_iff G _).mpr ⟨a,b,ha,ha',hb,hb',rfl⟩, ?_⟩
    rw [dilation_apply, hw]
    change (scale : ℂ) * ((a : ℂ)*G.omega1 + (b : ℂ)*G.omega2) =
      (a : ℂ)*((scale : ℂ)*G.omega1) + (b : ℂ)*((scale : ℂ)*G.omega2)
    ring
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨a,b,ha,ha',hb,hb',hz⟩ := (mem_cell_iff G z).mp hz
    apply (mem_cell_iff (scaledGeometry G) _).mpr
    refine ⟨a,b,ha,ha',hb,hb',?_⟩
    rw [dilation_apply, hz]
    change (scale : ℂ) * ((a : ℂ)*G.omega1 + (b : ℂ)*G.omega2) =
      (a : ℂ)*((scale : ℂ)*G.omega1) + (b : ℂ)*((scale : ℂ)*G.omega2)
    ring

theorem dilation_map_volume : Measure.map dilation (volume : Measure ℂ) =
    ENNReal.ofReal (1/2 : ℝ) • volume := by
  have h := Measure.map_addHaar_smul (volume : Measure ℂ) scale_pos.ne'
  simpa only [dilation, Homeomorph.smulOfNeZero_apply, Complex.finrank_real_complex,
    scale_sq, inv_eq_one_div, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] using h

theorem dilation_map_restricted (G : Geometry) :
    Measure.map dilation (volume.restrict (cell G)) =
      ENNReal.ofReal (1/2 : ℝ) • volume.restrict (cell (scaledGeometry G)) := by
  have h := dilation.toMeasurableEquiv.measurableEmbedding.restrict_map
    (volume : Measure ℂ) (cell (scaledGeometry G))
  change (Measure.map dilation volume).restrict (cell (scaledGeometry G)) =
    Measure.map dilation (volume.restrict (dilation ⁻¹' cell (scaledGeometry G))) at h
  rw [scaled_cell, Set.preimage_image_eq _ dilation.injective] at h
  rw [dilation_map_volume, Measure.restrict_smul, ← scaled_cell] at h
  exact h.symm

/-- The original charge-two measure is pushed to the original charge-one
measure on the scaled cell. Its 2/pi exactly cancels the area Jacobian2. -/
theorem dilation_measurePreserving (G : Geometry) :
    MeasurePreserving dilation (cellMeasure G 2) (cellMeasure (scaledGeometry G) 1) := by
  refine ⟨dilation.continuous.measurable, ?_⟩
  rw [cellMeasure, Measure.map_smul _ dilation.continuous.measurable.aemeasurable,
    dilation_map_restricted, smul_smul]
  unfold cellMeasure
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num

theorem scalingLinearEquiv_norm_sq (G : Geometry) (theta : Twist)
    (f : LLL (scaledGeometry G) (scaledTwist theta) 1) :
    ‖scalingLinearEquiv G theta f‖^2 = ‖f‖^2 := by
  rw [lll_norm_sq_eq_cellIntegral, lll_norm_sq_eq_cellIntegral]
  have h := (dilation_measurePreserving G).integral_comp
    dilation.toMeasurableEquiv.measurableEmbedding (fun w => ‖f.val w‖^2)
  simpa only [dilation_apply, scalingLinearEquiv_apply] using h

theorem scalingLinearEquiv_norm (G : Geometry) (theta : Twist)
    (f : LLL (scaledGeometry G) (scaledTwist theta) 1) :
    ‖scalingLinearEquiv G theta f‖ = ‖f‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (scalingLinearEquiv_norm_sq G theta f)

/-- Actual cell-Hilbert linear isometry, on the full physical carriers. -/
def scalingLinearIsometryEquiv (G : Geometry) (theta : Twist) :
    LLL (scaledGeometry G) (scaledTwist theta) 1 ≃ₗᵢ[ℂ] LLL G theta 2 :=
  { scalingLinearEquiv G theta with norm_map' := scalingLinearEquiv_norm G theta }

#print axioms dilation_apply
#print axioms scaled_cell
#print axioms dilation_map_volume
#print axioms dilation_map_restricted
#print axioms dilation_measurePreserving
#print axioms scalingLinearEquiv_norm_sq
#print axioms scalingLinearEquiv_norm
#print axioms scalingLinearIsometryEquiv

end TorusLean.Shared.ChargeTwoIsometry
