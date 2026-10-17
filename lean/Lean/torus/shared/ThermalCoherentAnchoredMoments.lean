import torus.shared.ThermalCoherentMomentsNorm

/-! Absolute plane moments of the original anchored-K scalar coefficients.
The two Gaussian L2 weights are deliberately different: 3/2 and 5/2
including each canonical jet's Gaussian. This gives strict geometric decay
in both indices. All integrals use the full plane dA/pi. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentAnchoredMoments
open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Shared.ThermalCoherentGaussian
open TorusLean.Shared.ThermalCoherentMoments
open scoped ComplexConjugate ENNReal

/-- Literal scalar coefficient of the original anchored plane kernel. -/
def anchoredPlaneCoefficient (j l : ℕ) (z : ℂ) : ℂ :=
  (thermalWeight 2 z : ℂ) * conj z^j * z^l * (Real.sqrt (2:ℝ):ℂ)^l /
    ((Real.sqrt (j.factorial:ℝ):ℂ)*(Real.sqrt (l.factorial:ℝ):ℂ))

theorem anchoredPlaneCoefficient_eq_weighted_jets (j l : ℕ) (z : ℂ) :
    anchoredPlaneCoefficient j l z = (Real.sqrt (2:ℝ):ℂ)^l *
      ((thermalWeight 1 z : ℂ) * (conj (planeJet j z)*planeJet l z)) := by
  have he : (thermalWeight 1 z : ℂ)*Complex.exp (-(‖z‖^2:ℂ)) =
      (thermalWeight 2 z : ℂ) := by
    simp only [thermalWeight,Complex.ofReal_exp]
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [planeJet_cross_factor]
  unfold anchoredPlaneCoefficient
  calc
    _ = (Real.sqrt (2:ℝ):ℂ)^l *
      (((thermalWeight 1 z : ℂ)*Complex.exp (-(‖z‖^2:ℂ))) * conj z^j * z^l /
        ((Real.sqrt (j.factorial:ℝ):ℂ)*(Real.sqrt (l.factorial:ℝ):ℂ))) := by rw [he]; ring
    _ = _ := by ring

theorem anchoredPlaneCoefficient_integrable (j l : ℕ) :
    Integrable (anchoredPlaneCoefficient j l) planeMeasure := by
  change Integrable (fun z => anchoredPlaneCoefficient j l z) planeMeasure
  simp_rw [anchoredPlaneCoefficient_eq_weighted_jets]
  exact (weighted_planeJet_cross_integrable 1 (by norm_num) j l).const_mul
    ((Real.sqrt (2:ℝ):ℂ)^l)

theorem anchoredPlaneCoefficient_integral (j l : ℕ) :
    (∫ z, anchoredPlaneCoefficient j l z ∂planeMeasure) =
      if j=l then (Real.sqrt (2:ℝ):ℂ)^l * ((2:ℂ)^(j+1))⁻¹ else 0 := by
  simp_rw [anchoredPlaneCoefficient_eq_weighted_jets]
  rw [integral_const_mul,weighted_planeJet_cross_integral 1 (by norm_num)]
  split_ifs with h
  · norm_num [thermalEigenvalue,Complex.ofReal_inv,Complex.ofReal_pow]
  · simp

private def weightedHalfNorm (a : ℝ) (j : ℕ) (z : ℂ) : ℝ :=
  Real.sqrt (thermalWeight a z)*‖planeJet j z‖

private theorem weightedHalfNorm_nonneg (a : ℝ) (j : ℕ) (z : ℂ) :
    0 ≤ weightedHalfNorm a j z := by unfold weightedHalfNorm; positivity

private theorem weightedHalfNorm_sq (a : ℝ) (j : ℕ) (z : ℂ) :
    weightedHalfNorm a j z ^2 = thermalWeight a z * ‖planeJet j z‖^2 := by
  rw [weightedHalfNorm,mul_pow,Real.sq_sqrt (thermalWeight_pos a z).le]

private theorem weightedHalfNorm_memLp (a : ℝ) (ha : 0<a) (j : ℕ) :
    MemLp (weightedHalfNorm a j) 2 planeMeasure := by
  have hc : Continuous (weightedHalfNorm a j) :=
    ((thermalWeight_continuous a).sqrt).mul (planeJet_continuous j).norm
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs,sq_abs,weightedHalfNorm_sq] using
    weighted_planeJet_sq_integrable a ha j

private theorem weightedHalfNorm_mul (a b : ℝ) (j l : ℕ) (z : ℂ) :
    weightedHalfNorm a j z * weightedHalfNorm b l z =
      thermalWeight ((a+b)/2) z * ‖planeJet j z‖ * ‖planeJet l z‖ := by
  have hs : thermalWeight ((a+b)/2) z ^2 = thermalWeight a z * thermalWeight b z := by
    unfold thermalWeight
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hh : Real.sqrt (thermalWeight a z)*Real.sqrt (thermalWeight b z) =
      thermalWeight ((a+b)/2) z := by
    rw [←Real.sqrt_mul (thermalWeight_pos a z).le,←hs,
      Real.sqrt_sq (thermalWeight_pos ((a+b)/2) z).le]
  unfold weightedHalfNorm
  calc
    _ = (Real.sqrt (thermalWeight a z)*Real.sqrt (thermalWeight b z))*
      ‖planeJet j z‖*‖planeJet l z‖ := by ring
    _ = _ := by rw [hh]

/-- Genuine asymmetric L2 Cauchy-Schwarz; both domains are proved from the
accepted exact plane moments before the inequality is used. -/
theorem asymmetric_planeJet_norm_cross_integral_le (a b : ℝ)
    (ha : 0<a) (hb : 0<b) (j l : ℕ) :
    (∫ z, thermalWeight ((a+b)/2) z*‖planeJet j z‖*‖planeJet l z‖ ∂planeMeasure) ≤
      Real.sqrt (thermalEigenvalue a j)*Real.sqrt (thermalEigenvalue b l) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (weightedHalfNorm_nonneg a j))
    (Filter.Eventually.of_forall (weightedHalfNorm_nonneg b l))
    (by simpa using weightedHalfNorm_memLp a ha j)
    (by simpa using weightedHalfNorm_memLp b hb l)
  simp only [weightedHalfNorm_mul,Real.rpow_two,weightedHalfNorm_sq,
    weighted_planeJet_sq_integral a ha,weighted_planeJet_sq_integral b hb,
    ←Real.sqrt_eq_rpow] at h
  exact h

theorem anchoredPlaneCoefficient_integral_norm_le_roots (j l : ℕ) :
    (∫ z, ‖anchoredPlaneCoefficient j l z‖ ∂planeMeasure) ≤
      (Real.sqrt (2:ℝ))^l * Real.sqrt (thermalEigenvalue (1/2) j) *
        Real.sqrt (thermalEigenvalue (3/2) l) := by
  have he (z : ℂ) : ‖anchoredPlaneCoefficient j l z‖ =
      (Real.sqrt (2:ℝ))^l*(thermalWeight 1 z*‖planeJet j z‖*‖planeJet l z‖) := by
    rw [anchoredPlaneCoefficient_eq_weighted_jets]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (2:ℝ)),abs_of_pos (thermalWeight_pos 1 z),Complex.norm_conj]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have h := asymmetric_planeJet_norm_cross_integral_le (1/2) (3/2)
    (by norm_num) (by norm_num) j l
  norm_num only [show ((1/2:ℝ)+3/2)/2=1 by norm_num] at h
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (by positivity : 0≤(Real.sqrt (2:ℝ))^l)

private theorem sqrt_thermalEigenvalue_eq (a : ℝ) (ha : 0<a) (j : ℕ) :
    Real.sqrt (thermalEigenvalue a j) = Real.sqrt ((1+a)⁻¹)^(j+1) := by
  have hp (n : ℕ) : Real.sqrt (((1+a)⁻¹)^n) = Real.sqrt ((1+a)⁻¹)^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [thermalEigenvalue,←inv_pow,hp]

/-- Both indices strictly decay. The asymmetric split avoids the critical
spectator direction produced by equal Gaussian allocations. -/
theorem anchoredPlaneCoefficient_integral_norm_le (j l : ℕ) :
    (∫ z, ‖anchoredPlaneCoefficient j l z‖ ∂planeMeasure) ≤
      (2/Real.sqrt (15:ℝ)) * (Real.sqrt (2/3:ℝ))^j * (Real.sqrt (4/5:ℝ))^l := by
  refine (anchoredPlaneCoefficient_integral_norm_le_roots j l).trans_eq ?_
  rw [sqrt_thermalEigenvalue_eq (1/2) (by norm_num),
    sqrt_thermalEigenvalue_eq (3/2) (by norm_num)]
  norm_num only [show (1+(1/2:ℝ))⁻¹=2/3 by norm_num,
    show (1+(3/2:ℝ))⁻¹=2/5 by norm_num]
  rw [pow_succ,pow_succ]
  have hc : Real.sqrt (2/3:ℝ)*Real.sqrt (2/5:ℝ)=2/Real.sqrt (15:ℝ) := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2/3),show (2/3:ℝ)*(2/5)=4/15 by norm_num,
      Real.sqrt_div (by norm_num : (0:ℝ)≤4)]
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
  have hr : Real.sqrt (2:ℝ)*Real.sqrt (2/5:ℝ)=Real.sqrt (4/5:ℝ) := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  calc
    _ = (Real.sqrt (2/3:ℝ)*Real.sqrt (2/5:ℝ))*Real.sqrt (2/3:ℝ)^j*
      (Real.sqrt (2:ℝ)*Real.sqrt (2/5:ℝ))^l := by rw [mul_pow]; ring
    _ = _ := by rw [hc,hr]

end TorusLean.Shared.ThermalCoherentAnchoredMoments
