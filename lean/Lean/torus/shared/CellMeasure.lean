import torus.shared.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The actual physical cell measure and raw-section integral

The cell is the image of `[0,1) × [0,1)` under the actual lattice basis.
Its measure is `(k / π)` times restricted two-dimensional Lebesgue measure,
with total mass `k*M`. No dimension, frame, reproducing kernel or completeness
assumption is a field of the geometry or of this construction.

The final positivity theorem uses continuity and uniqueness of the entire
holomorphic factor, rather than substituting a finite coordinate space.
-/

set_option autoImplicit false

namespace TorusLean.Shared

open Set MeasureTheory
open scoped ComplexConjugate Topology

noncomputable section

/-- The actual real-linear map `a + i*b ↦ a*ω₁ + b*ω₂`. -/
def cellCoordinateMap (G : Geometry) : ℂ →ₗ[ℝ] ℂ :=
  Complex.reLm.smulRight G.omega1 + Complex.imLm.smulRight G.omega2

theorem cellCoordinateMap_apply (G : Geometry) (z : ℂ) :
    cellCoordinateMap G z = (z.re : ℂ) * G.omega1 + (z.im : ℂ) * G.omega2 := by
  simp [cellCoordinateMap, Complex.real_smul]

theorem cellCoordinateMap_det (G : Geometry) :
    LinearMap.det (cellCoordinateMap G) = Real.pi * (G.M : ℝ) := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  have ha := G.area
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at ha
  simpa [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, cellCoordinateMap_apply, Complex.mul_re,
    Complex.mul_im, sub_eq_add_neg, mul_comm] using ha

theorem cellCoordinateMap_det_pos (G : Geometry) :
    0 < LinearMap.det (cellCoordinateMap G) := by
  rw [cellCoordinateMap_det]
  exact mul_pos Real.pi_pos (Nat.cast_pos.mpr G.flux_pos)

/-- Legal flux makes the actual lattice coordinates invertible. -/
def cellCoordinateEquiv (G : Geometry) : ℂ ≃ₗ[ℝ] ℂ :=
  LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr
    (cellCoordinateMap_det_pos G).ne')

theorem cellCoordinateEquiv_apply (G : Geometry) (z : ℂ) :
    cellCoordinateEquiv G z = (z.re : ℂ) * G.omega1 + (z.im : ℂ) * G.omega2 := by
  rw [cellCoordinateEquiv, LinearMap.equivOfIsUnitDet_apply, cellCoordinateMap_apply]

private def unitSquare : Set ℂ :=
  {z | z.re ∈ Ico (0 : ℝ) 1 ∧ z.im ∈ Ico (0 : ℝ) 1}

private def closedUnitSquare : Set ℂ :=
  {z | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Icc (0 : ℝ) 1}

private def openUnitSquare : Set ℂ :=
  {z | z.re ∈ Ioo (0 : ℝ) 1 ∧ z.im ∈ Ioo (0 : ℝ) 1}

private theorem unitSquare_measurable : MeasurableSet unitSquare :=
  (measurableSet_Ico.preimage Complex.continuous_re.measurable).inter
    (measurableSet_Ico.preimage Complex.continuous_im.measurable)

private theorem volume_unitSquare : volume unitSquare = 1 := by
  change volume (Complex.measurableEquivRealProd ⁻¹'
    (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)) = 1
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  change (volume : Measure ℝ).prod volume (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num

/-- The canonical half-open fundamental cell, with the original basis order. -/
def cell (G : Geometry) : Set ℂ := cellCoordinateEquiv G '' unitSquare

theorem mem_cell_iff (G : Geometry) (z : ℂ) :
    z ∈ cell G ↔ ∃ a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧ b < 1 ∧
      z = (a : ℂ) * G.omega1 + (b : ℂ) * G.omega2 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.re, w.im, hw.1.1, hw.1.2, hw.2.1, hw.2.2,
      cellCoordinateEquiv_apply G w⟩
  · rintro ⟨a, b, ha, ha', hb, hb', hz⟩
    refine ⟨a + b * Complex.I, ?_, ?_⟩
    · simpa [unitSquare] using And.intro (And.intro ha ha') (And.intro hb hb')
    · simpa [cellCoordinateEquiv_apply] using hz.symm

theorem measurableSet_cell (G : Geometry) : MeasurableSet (cell G) :=
  (MeasurableEquiv.measurableSet_image
    (cellCoordinateEquiv G).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv).mpr
      unitSquare_measurable

theorem volume_cell (G : Geometry) : volume (cell G) =
    ENNReal.ofReal (Real.pi * (G.M : ℝ)) := by
  change volume ((cellCoordinateEquiv G : ℂ →ₗ[ℝ] ℂ) '' unitSquare) = _
  rw [Measure.addHaar_image_linearMap, volume_unitSquare, mul_one]
  simp only [cellCoordinateEquiv, LinearMap.coe_equivOfIsUnitDet,
    cellCoordinateMap_det, abs_of_pos (mul_pos Real.pi_pos
      (Nat.cast_pos.mpr G.flux_pos))]

/-- Physical charge measure: its mass is `k*M`, not one. -/
def cellMeasure (G : Geometry) (k : ℕ) : Measure ℂ :=
  ENNReal.ofReal ((k : ℝ) / Real.pi) • volume.restrict (cell G)

theorem cellMeasure_univ (G : Geometry) (k : ℕ) :
    cellMeasure G k univ = ENNReal.ofReal ((k * G.M : ℕ) : ℝ) := by
  rw [cellMeasure, Measure.smul_apply, Measure.restrict_apply_univ, volume_cell,
    smul_eq_mul, ← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg k) Real.pi_pos.le)]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

instance cellMeasure_isFiniteMeasure (G : Geometry) (k : ℕ) :
    IsFiniteMeasure (cellMeasure G k) :=
  ⟨by rw [cellMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem cellMeasure_zero_charge (G : Geometry) : cellMeasure G 0 = 0 := by
  simp [cellMeasure]

theorem cellMeasure_scale_pos (k : ℕ) (hk : 0 < k) :
    0 < ENNReal.ofReal ((k : ℝ) / Real.pi) :=
  ENNReal.ofReal_pos.mpr (div_pos (Nat.cast_pos.mpr hk) Real.pi_pos)

/-- A compact containing the half-open cell, used solely for integrability. -/
def closedCell (G : Geometry) : Set ℂ := cellCoordinateEquiv G '' closedUnitSquare

theorem isCompact_closedCell (G : Geometry) : IsCompact (closedCell G) := by
  have hc : IsCompact closedUnitSquare := by
    exact isCompact_Icc.reProdIm isCompact_Icc
  exact hc.image (cellCoordinateEquiv G).toContinuousLinearEquiv.continuous

theorem cell_subset_closedCell (G : Geometry) : cell G ⊆ closedCell G := by
  apply image_mono
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.le⟩, ⟨hz.2.1, hz.2.2.le⟩⟩

/-- A genuine nonempty open subset of the half-open physical cell. -/
def openCell (G : Geometry) : Set ℂ := cellCoordinateEquiv G '' openUnitSquare

theorem isOpen_openCell (G : Geometry) : IsOpen (openCell G) := by
  have ho : IsOpen openUnitSquare :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  exact (cellCoordinateEquiv G).toContinuousLinearEquiv.toHomeomorph.isOpenMap _ ho

theorem openCell_subset_cell (G : Geometry) : openCell G ⊆ cell G := by
  apply image_mono
  intro z hz
  exact ⟨⟨hz.1.1.le, hz.1.2⟩, ⟨hz.2.1.le, hz.2.2⟩⟩

theorem openCell_nonempty (G : Geometry) : (openCell G).Nonempty := by
  refine ⟨cellCoordinateEquiv G ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Complex.I), ?_⟩
  apply mem_image_of_mem
  norm_num [openUnitSquare]

/-- Every actual continuous universal-cover function is integrable in the cell. -/
theorem continuous_integrable_cellMeasure (G : Geometry) (k : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} (hf : Continuous f) : Integrable f (cellMeasure G k) := by
  have hfi : IntegrableOn f (cell G) volume :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedCell G)).mono_set
      (cell_subset_closedCell G)
  exact hfi.smul_measure ENNReal.ofReal_ne_top

theorem gaussianFactor_continuous (k : ℝ) :
    Continuous (TorusLean.Geometry.gaussianFactor k) := by
  unfold TorusLean.Geometry.gaussianFactor
  exact Complex.continuous_exp.comp
    ((continuous_const.mul (continuous_id.mul Complex.continuous_conj)).div_const 2)

theorem gaussianHolomorphic_continuous (k : ℝ) (f : ℂ → ℂ)
    (hf : TorusLean.Geometry.IsGaussianHolomorphic k f) : Continuous f := by
  obtain ⟨F, hF, hf⟩ := hf
  have heq : f = fun z => TorusLean.Geometry.gaussianFactor k z * F z := funext hf
  rw [heq]
  exact (gaussianFactor_continuous k).mul hF.continuous

theorem rawLLL_continuous (G : Geometry) (theta : Twist) (k : ℕ)
    (f : RawLLL G theta k) : Continuous f.val :=
  gaussianHolomorphic_continuous (k : ℝ) f.val f.property.1

/-- Actual cell sesquilinear integral, conjugate-linear in its first argument. -/
def cellInner (G : Geometry) (k : ℕ) (f g : ℂ → ℂ) : ℂ :=
  ∫ z, conj (f z) * g z ∂cellMeasure G k

/-- The same physical integral on the existing raw-section carrier. -/
def rawCellInner (G : Geometry) (theta : Twist) (k : ℕ)
    (f g : RawLLL G theta k) : ℂ := cellInner G k f.val g.val

theorem cellInner_integrable (G : Geometry) (k : ℕ) (f g : ℂ → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun z => conj (f z) * g z) (cellMeasure G k) :=
  continuous_integrable_cellMeasure G k ((Complex.continuous_conj.comp hf).mul hg)

theorem rawCellInner_integrable (G : Geometry) (theta : Twist) (k : ℕ)
    (f g : RawLLL G theta k) :
    Integrable (fun z => conj (f.val z) * g.val z) (cellMeasure G k) :=
  cellInner_integrable G k f.val g.val (rawLLL_continuous G theta k f)
    (rawLLL_continuous G theta k g)

theorem cellInner_conj_symm (G : Geometry) (k : ℕ) (f g : ℂ → ℂ) :
    conj (cellInner G k f g) = cellInner G k g f := by
  rw [cellInner, ← integral_conj]
  simp only [map_mul, Complex.conj_conj]
  simp only [cellInner, mul_comm]

theorem cellInner_self (G : Geometry) (k : ℕ) (f : ℂ → ℂ) :
    cellInner G k f f = ((∫ z, ‖f z‖ ^ 2 ∂cellMeasure G k : ℝ) : ℂ) := by
  simp only [cellInner, Complex.conj_mul', ← Complex.ofReal_pow]
  exact integral_complex_ofReal

theorem cellInner_self_re_nonneg (G : Geometry) (k : ℕ) (f : ℂ → ℂ) :
    0 ≤ (cellInner G k f f).re := by
  rw [cellInner_self, Complex.ofReal_re]
  exact integral_nonneg (fun z => sq_nonneg ‖f z‖)

theorem cellInner_add_right (G : Geometry) (k : ℕ) (f g h : ℂ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    cellInner G k f (g + h) = cellInner G k f g + cellInner G k f h := by
  simp only [cellInner, Pi.add_apply, mul_add]
  exact integral_add (cellInner_integrable G k f g hf hg)
    (cellInner_integrable G k f h hf hh)

theorem cellInner_smul_right (G : Geometry) (k : ℕ) (c : ℂ) (f g : ℂ → ℂ) :
    cellInner G k f (c • g) = c * cellInner G k f g := by
  simp only [cellInner, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (conj (f _)) c, mul_assoc]
  exact integral_const_mul c _

theorem cellInner_add_left (G : Geometry) (k : ℕ) (f g h : ℂ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    cellInner G k (f + g) h = cellInner G k f h + cellInner G k g h := by
  simp only [cellInner, Pi.add_apply, map_add, add_mul]
  exact integral_add (cellInner_integrable G k f h hf hh)
    (cellInner_integrable G k g h hg hh)

theorem cellInner_smul_left (G : Geometry) (k : ℕ) (c : ℂ) (f g : ℂ → ℂ) :
    cellInner G k (c • f) g = conj c * cellInner G k f g := by
  simp only [cellInner, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact integral_const_mul (conj c) _

/-- Zero a.e. in the actual cell determines a Gaussian-holomorphic function
globally. Positive charge is required because the charge-zero measure is zero.
The proof uses the entire factor, never a dimension or reproducing-kernel input. -/
theorem gaussianHolomorphic_eq_zero_of_cell_ae (G : Geometry) (k : ℕ)
    (hk : 0 < k) (f : ℂ → ℂ)
    (hf : TorusLean.Geometry.IsGaussianHolomorphic (k : ℝ) f)
    (hzero : f =ᵐ[cellMeasure G k] 0) : f = 0 := by
  have hfcont := gaussianHolomorphic_continuous (k : ℝ) f hf
  have hscale : ENNReal.ofReal ((k : ℝ) / Real.pi) ≠ 0 :=
    (cellMeasure_scale_pos k hk).ne'
  have hcell : f =ᵐ[volume.restrict (cell G)] 0 :=
    (Measure.ae_ennreal_smul_measure_iff hscale).mp hzero
  have hopen : f =ᵐ[volume.restrict (openCell G)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (openCell_subset_cell G) hcell
  have hpoint : EqOn f 0 (openCell G) :=
    Measure.eqOn_open_of_ae_eq hopen (isOpen_openCell G) hfcont.continuousOn
      continuous_const.continuousOn
  obtain ⟨F, hF, hfactor⟩ := hf
  have hFpoint : EqOn F 0 (openCell G) := by
    intro z hz
    have hprod : TorusLean.Geometry.gaussianFactor (k : ℝ) z * F z = 0 :=
      (hfactor z).symm.trans (hpoint hz)
    exact (mul_eq_zero.mp hprod).resolve_left
      (TorusLean.Geometry.gaussianFactor_ne_zero (k : ℝ) z)
  obtain ⟨z₀, hz₀⟩ := openCell_nonempty G
  have hevent : F =ᶠ[𝓝 z₀] 0 :=
    Filter.mem_of_superset ((isOpen_openCell G).mem_nhds hz₀)
      (fun _ hz => hFpoint hz)
  have hanalytic : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  have hFzero : F = 0 := hanalytic.eq_of_eventuallyEq analyticOnNhd_const hevent
  funext z
  rw [hfactor z, hFzero]
  simp

/-- Nondegeneracy of the actual cell integral on Gaussian-holomorphic sections. -/
theorem cellInner_self_eq_zero_iff (G : Geometry) (k : ℕ) (hk : 0 < k)
    (f : ℂ → ℂ) (hf : TorusLean.Geometry.IsGaussianHolomorphic (k : ℝ) f) :
    cellInner G k f f = 0 ↔ f = 0 := by
  rw [cellInner_self, Complex.ofReal_eq_zero]
  constructor
  · intro hzero
    have hfi : Integrable (fun z => ‖f z‖ ^ 2) (cellMeasure G k) :=
      continuous_integrable_cellMeasure G k
        ((gaussianHolomorphic_continuous (k : ℝ) f hf).norm.pow 2)
    have hae : (fun z => ‖f z‖ ^ 2) =ᵐ[cellMeasure G k] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖f z‖) hfi).mp hzero
    have hfae : f =ᵐ[cellMeasure G k] 0 := by
      filter_upwards [hae] with z hz
      exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
    exact gaussianHolomorphic_eq_zero_of_cell_ae G k hk f hf hfae
  · rintro rfl
    simp

theorem cellInner_self_re_eq_zero_iff (G : Geometry) (k : ℕ) (hk : 0 < k)
    (f : ℂ → ℂ) (hf : TorusLean.Geometry.IsGaussianHolomorphic (k : ℝ) f) :
    (cellInner G k f f).re = 0 ↔ f = 0 := by
  rw [← cellInner_self_eq_zero_iff G k hk f hf, cellInner_self,
    Complex.ofReal_re, Complex.ofReal_eq_zero]

theorem rawCellInner_self_eq_zero_iff (G : Geometry) (theta : Twist) (k : ℕ)
    (hk : 0 < k) (f : RawLLL G theta k) :
    rawCellInner G theta k f f = 0 ↔ f.val = 0 :=
  cellInner_self_eq_zero_iff G k hk f.val f.property.1

theorem rawCellInner_self_re_pos (G : Geometry) (theta : Twist) (k : ℕ)
    (hk : 0 < k) (f : RawLLL G theta k) (hf : f.val ≠ 0) :
    0 < (rawCellInner G theta k f f).re := by
  apply lt_of_le_of_ne (cellInner_self_re_nonneg G k f.val)
  exact Ne.symm (mt (cellInner_self_re_eq_zero_iff G k hk f.val f.property.1).mp hf)

#print axioms cellCoordinateMap_det
#print axioms cellCoordinateMap_det_pos
#print axioms mem_cell_iff
#print axioms measurableSet_cell
#print axioms volume_cell
#print axioms cellMeasure_univ
#print axioms cellMeasure_zero_charge
#print axioms cellMeasure_scale_pos
#print axioms isCompact_closedCell
#print axioms cell_subset_closedCell
#print axioms isOpen_openCell
#print axioms openCell_subset_cell
#print axioms openCell_nonempty
#print axioms continuous_integrable_cellMeasure
#print axioms gaussianFactor_continuous
#print axioms gaussianHolomorphic_continuous
#print axioms rawLLL_continuous
#print axioms cellInner_integrable
#print axioms rawCellInner_integrable
#print axioms cellInner_conj_symm
#print axioms cellInner_self
#print axioms cellInner_self_re_nonneg
#print axioms cellInner_add_right
#print axioms cellInner_smul_right
#print axioms cellInner_add_left
#print axioms cellInner_smul_left
#print axioms gaussianHolomorphic_eq_zero_of_cell_ae
#print axioms cellInner_self_eq_zero_iff
#print axioms cellInner_self_re_eq_zero_iff
#print axioms rawCellInner_self_eq_zero_iff
#print axioms rawCellInner_self_re_pos

end

end TorusLean.Shared
