import torus.geometry.MagneticTranslation
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual planar magnetic L2 norm and inner-product preservation.
The action is the canonical magneticTranslate on complex-valued functions;
the measure is ordinary two-dimensional Lebesgue volume divided by pi.
This ambient L2 space is not a replacement physical torus LLL or cell metric. -/

set_option autoImplicit false

namespace TorusLean.Fermion.PlaneMagneticUnitary

open MeasureTheory TorusLean.Geometry
open scoped ComplexConjugate ENNReal

noncomputable section

/-- The paper's charge-one plane measure d²z/pi on the actual complex plane. -/
def planeMeasure : Measure ℂ := ENNReal.ofReal (1 / Real.pi) • volume

/-- Actual Bochner integral, conjugate-linear first. On MemLp functions it
coincides with the genuine L2 inner product, as proved below. -/
def planeInner (f g : ℂ → ℂ) : ℂ := ∫ z, conj (f z) * g z ∂planeMeasure

theorem planeMeasure_scale_pos : 0 < ENNReal.ofReal (1 / Real.pi) :=
  ENNReal.ofReal_pos.mpr (one_div_pos.mpr Real.pi_pos)

/-- The complex plane measure is exactly normalized ordinary real 2D volume. -/
theorem planeMeasure_map_real_prod :
    Measure.map Complex.measurableEquivRealProd planeMeasure =
      ENNReal.ofReal (1 / Real.pi) • (volume : Measure (ℝ × ℝ)) := by
  rw [planeMeasure, Measure.map_smul (ENNReal.ofReal (1 / Real.pi))
    Complex.volume_preserving_equiv_real_prod.aemeasurable,
    Complex.volume_preserving_equiv_real_prod.map_eq]

theorem planeMeasure_translate (x : ℂ) :
    MeasurePreserving (fun z : ℂ => z - x) planeMeasure planeMeasure := by
  unfold planeMeasure
  exact measurePreserving_sub_right _ x

theorem magnetic_cross_pointwise (k : ℝ) (x z : ℂ) (f g : ℂ → ℂ) :
    conj (magneticTranslate k x f z) * magneticTranslate k x g z =
      conj (f (z - x)) * g (z - x) := by
  have hm : conj (Complex.exp (magneticExponent k z x)) *
      Complex.exp (magneticExponent k z x) = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      magneticMultiplier_norm]
    norm_num
  simp only [magneticTranslate, map_mul]
  calc
    _ = (conj (Complex.exp (magneticExponent k z x)) *
        Complex.exp (magneticExponent k z x)) * (conj (f (z-x)) * g (z-x)) := by ring
    _ = _ := by rw [hm, one_mul]

/-- Exact integral identity. Integrability/L2 membership is not inferred
from total Bochner-integral equality; the domain bridge is separate below. -/
theorem planeInner_translate (k : ℝ) (x : ℂ) (f g : ℂ → ℂ) :
    planeInner (magneticTranslate k x f) (magneticTranslate k x g) =
      planeInner f g := by
  unfold planeInner
  simp_rw [magnetic_cross_pointwise]
  unfold planeMeasure
  exact integral_sub_right_eq_self (fun z : ℂ => conj (f z) * g z) x

theorem plane_square_integral_translate (k : ℝ) (x : ℂ) (f : ℂ → ℂ) :
    (∫ z, ‖magneticTranslate k x f z‖^2 ∂planeMeasure) =
      ∫ z, ‖f z‖^2 ∂planeMeasure := by
  simp_rw [magneticTranslate_norm]
  unfold planeMeasure
  exact integral_sub_right_eq_self (fun z : ℂ => ‖f z‖^2) x

theorem magnetic_aestronglyMeasurable (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f planeMeasure) :
    AEStronglyMeasurable (magneticTranslate k x f) planeMeasure := by
  have hc : Continuous (fun z : ℂ => Complex.exp (magneticExponent k z x)) := by
    unfold magneticExponent
    fun_prop
  have hs := hf.comp_measurePreserving (planeMeasure_translate x)
  exact hc.aestronglyMeasurable.mul hs

theorem magnetic_memLp (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : MemLp f 2 planeMeasure) : MemLp (magneticTranslate k x f) 2 planeMeasure := by
  have hs := hf.comp_measurePreserving (planeMeasure_translate x)
  exact hs.congr_norm (magnetic_aestronglyMeasurable k x f hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z => (magneticTranslate_norm k x z f).symm))

theorem magnetic_memLp_iff (k : ℝ) (x : ℂ) (f : ℂ → ℂ) :
    MemLp (magneticTranslate k x f) 2 planeMeasure ↔ MemLp f 2 planeMeasure := by
  constructor
  · intro hf
    have h := magnetic_memLp k (-x) (magneticTranslate k x f) hf
    have hinv := magneticTranslate_inverse k (-x) f
    simp only [neg_neg] at hinv
    rwa [hinv] at h
  · exact magnetic_memLp k x f

theorem magnetic_eLpNorm (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f planeMeasure) :
    eLpNorm (magneticTranslate k x f) 2 planeMeasure = eLpNorm f 2 planeMeasure := by
  calc
    _ = eLpNorm (fun z : ℂ => f (z-x)) 2 planeMeasure :=
      eLpNorm_congr_norm_ae (magnetic_aestronglyMeasurable k x f hf)
        (hf.comp_measurePreserving (planeMeasure_translate x))
        (Filter.Eventually.of_forall (fun z => magneticTranslate_norm k x z f))
    _ = _ := eLpNorm_comp_measurePreserving hf (planeMeasure_translate x)

theorem magnetic_norm_toLp (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : MemLp f 2 planeMeasure) :
    ‖(magnetic_memLp k x f hf).toLp (magneticTranslate k x f)‖ = ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp, magnetic_eLpNorm k x f hf.aestronglyMeasurable]

theorem planeInner_eq_L2_inner (f g : ℂ → ℂ)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    planeInner f g = inner ℂ (hf.toLp f) (hg.toLp g) := by
  rw [MeasureTheory.L2.inner_def]
  unfold planeInner
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hzf hzg
  rw [hzf, hzg, RCLike.inner_apply']

theorem planeInner_integrable (f g : ℂ → ℂ)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    Integrable (fun z : ℂ => conj (f z) * g z) planeMeasure := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  apply h.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hzf hzg
  rw [hzf, hzg, RCLike.inner_apply']

/-- The canonical magnetic action on genuine Lebesgue L2 equivalence classes. -/
def magneticL2 (k : ℝ) (x : ℂ) (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  (magnetic_memLp k x f (Lp.memLp f)).toLp (magneticTranslate k x f)

theorem magneticL2_coe (k : ℝ) (x : ℂ) (f : Lp ℂ 2 planeMeasure) :
    (magneticL2 k x f : ℂ → ℂ) =ᵐ[planeMeasure] magneticTranslate k x f :=
  (magnetic_memLp k x f (Lp.memLp f)).coeFn_toLp

theorem magneticL2_norm (k : ℝ) (x : ℂ) (f : Lp ℂ 2 planeMeasure) :
    ‖magneticL2 k x f‖ = ‖f‖ := by
  unfold magneticL2
  rw [magnetic_norm_toLp k x f (Lp.memLp f), Lp.toLp_coeFn f (Lp.memLp f)]

/-- On each actual L2 function, the quotient operator is its existing
pointwise magneticTranslate, not an unspecified isometry of L2. -/
theorem magneticL2_toLp (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : MemLp f 2 planeMeasure) :
    magneticL2 k x (hf.toLp f) =
      (magnetic_memLp k x f hf).toLp (magneticTranslate k x f) := by
  apply Lp.ext
  have hs := hf.coeFn_toLp.comp_tendsto
    (planeMeasure_translate x).quasiMeasurePreserving.tendsto_ae
  filter_upwards [magneticL2_coe k x (hf.toLp f),
    (magnetic_memLp k x f hf).coeFn_toLp, hs] with z hz htz hshift
  simp only [Function.comp_apply] at hshift
  rw [hz, htz]
  simp only [magneticTranslate]
  rw [hshift]

theorem magneticL2_inverse (k : ℝ) (x : ℂ) (f : Lp ℂ 2 planeMeasure) :
    magneticL2 k x (magneticL2 k (-x) f) = f := by
  apply Lp.ext
  have hi := (magneticL2_coe k (-x) f).comp_tendsto
    (planeMeasure_translate x).quasiMeasurePreserving.tendsto_ae
  filter_upwards [magneticL2_coe k x (magneticL2 k (-x) f), hi] with z hz hzi
  calc
    _ = magneticTranslate k x (magneticL2 k (-x) f) z := hz
    _ = magneticTranslate k x (magneticTranslate k (-x) f) z := by
      simp only [Function.comp_apply, magneticTranslate] at hzi ⊢
      rw [hzi]
    _ = f z := congrFun (magneticTranslate_inverse k x f) z

theorem magneticL2_add (k : ℝ) (x : ℂ) (f g : Lp ℂ 2 planeMeasure) :
    magneticL2 k x (f + g) = magneticL2 k x f + magneticL2 k x g := by
  apply Lp.ext
  have ha := (Lp.coeFn_add f g).comp_tendsto
    (planeMeasure_translate x).quasiMeasurePreserving.tendsto_ae
  filter_upwards [magneticL2_coe k x (f+g), magneticL2_coe k x f,
    magneticL2_coe k x g, Lp.coeFn_add (magneticL2 k x f) (magneticL2 k x g), ha]
    with z hz hfz hgz hsum hshift
  simp only [Function.comp_apply, Pi.add_apply] at hsum hshift
  rw [hz, hsum, hfz, hgz]
  simp only [magneticTranslate]
  rw [hshift]
  exact mul_add _ _ _

theorem magneticL2_smul (k : ℝ) (x : ℂ) (c : ℂ) (f : Lp ℂ 2 planeMeasure) :
    magneticL2 k x (c • f) = c • magneticL2 k x f := by
  apply Lp.ext
  have hs := (Lp.coeFn_smul c f).comp_tendsto
    (planeMeasure_translate x).quasiMeasurePreserving.tendsto_ae
  filter_upwards [magneticL2_coe k x (c • f), magneticL2_coe k x f,
    Lp.coeFn_smul c (magneticL2 k x f), hs] with z hz hfz hsmul hshift
  simp only [Function.comp_apply, Pi.smul_apply] at hsmul hshift
  rw [hz, hsmul, hfz]
  simp only [magneticTranslate]
  rw [hshift]
  simp only [smul_eq_mul]
  ring

/-- A genuine unitary magnetic translation on ambient planar L2, with
derived linearity, norm preservation and inverse; no such field is an input. -/
def magneticL2Equiv (k : ℝ) (x : ℂ) :
    Lp ℂ 2 planeMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 planeMeasure where
  toFun := magneticL2 k x
  invFun := magneticL2 k (-x)
  left_inv := by
    intro f
    simpa only [neg_neg] using magneticL2_inverse k (-x) f
  right_inv := magneticL2_inverse k x
  map_add' := magneticL2_add k x
  map_smul' := magneticL2_smul k x
  norm_map' := magneticL2_norm k x

theorem magneticL2Equiv_apply (k : ℝ) (x : ℂ) (f : Lp ℂ 2 planeMeasure) :
    magneticL2Equiv k x f = magneticL2 k x f := rfl

theorem magneticL2Equiv_coe (k : ℝ) (x : ℂ) (f : Lp ℂ 2 planeMeasure) :
    (magneticL2Equiv k x f : ℂ → ℂ) =ᵐ[planeMeasure] magneticTranslate k x f :=
  magneticL2_coe k x f

theorem magneticL2_inner (k : ℝ) (x : ℂ) (f g : Lp ℂ 2 planeMeasure) :
    inner ℂ (magneticL2 k x f) (magneticL2 k x g) = inner ℂ f g :=
  (magneticL2Equiv k x).inner_map_map f g

/-- Cauchy-Schwarz for the actual magnetic action, using derived L2 isometry.
There is no oscillator-diagonal or jet-envelope premise. -/
theorem displacement_modulus_le_norm_sq (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : MemLp f 2 planeMeasure) :
    ‖planeInner f (magneticTranslate k x f)‖ ≤ ‖hf.toLp f‖^2 := by
  rw [planeInner_eq_L2_inner f (magneticTranslate k x f) hf (magnetic_memLp k x f hf)]
  have h := norm_inner_le_norm (𝕜 := ℂ) (hf.toLp f)
    ((magnetic_memLp k x f hf).toLp (magneticTranslate k x f))
  rwa [magnetic_norm_toLp k x f hf, ← pow_two] at h

/-- Actual unit-vector matrix-element bound. Normalization of the canonical
planeJet j has not been assumed for all j or identified with a cell jet norm. -/
theorem normalized_displacement_modulus (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : MemLp f 2 planeMeasure) (hn : ‖hf.toLp f‖ = 1) :
    ‖planeInner f (magneticTranslate k x f)‖ ≤ 1 := by
  have h := displacement_modulus_le_norm_sq k x f hf
  simpa only [hn, one_pow] using h

end
end TorusLean.Fermion.PlaneMagneticUnitary
