import torus.shared.ParameterCellAdjointStokes

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterCellAdjoint
open MeasureTheory TorusLean.Geometry
open scoped ComplexConjugate

/-- The two original dual magnetic multipliers cancel in the actual
sesquilinear product. Individual parameter sections need not be periodic. -/
theorem dual_cross_periodic (G : Geometry) (theta : Twist) (k : ℕ)
    (f g : ℂ → ℂ) (hf : HasDualBoundary G theta k f) (hg : HasDualBoundary G theta k g) :
    ∀ p : ℤ × ℤ, ∀ z : ℂ,
      conj (f (latticePeriod G.omega1 G.omega2 p + z)) *
        g (latticePeriod G.omega1 G.omega2 p + z) = conj (f z) * g z := by
  intro p z
  have hfb := (latticeBoundary_iff_forward G.M k G.omega1 G.omega2
    theta.theta1 theta.theta2 (fun R => conj (f R))).mp hf p z
  have hgb := (latticeBoundary_iff_forward G.M k G.omega1 G.omega2
    theta.theta1 theta.theta2 (fun R => conj (g R))).mp hg p z
  let m : ℂ := (latticeChi G.M theta.theta1 theta.theta2 p ^ k)⁻¹ *
    Complex.exp (magneticExponent (k:ℝ) z (latticePeriod G.omega1 G.omega2 p))
  have hm : ‖m‖ = 1 := by
    simp only [m, norm_mul, norm_inv, norm_pow, latticeChi_norm,
      magneticMultiplier_norm, one_pow, inv_one, one_mul]
  have hunit : m * conj m = 1 := by rw [Complex.mul_conj', hm]; norm_num
  have hgg : g (z+latticePeriod G.omega1 G.omega2 p) = conj m * g z := by
    simpa only [m, map_mul, Complex.conj_conj] using congrArg (conj : ℂ → ℂ) hgb
  rw [add_comm (latticePeriod G.omega1 G.omega2 p) z, hfb, hgg]
  change (m * conj (f z)) * (conj m * g z) = _
  calc
    _ = (m*conj m)*(conj (f z)*g z) := by ring
    _ = _ := by rw [hunit, one_mul]

theorem dual_cell_direction_integrationByParts (G : Geometry) (theta : Twist) (k : ℕ)
    (f g : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfb : HasDualBoundary G theta k f) (hgb : HasDualBoundary G theta k g) (v : ℂ) :
    cellInner G k (fun R => (fderiv ℝ f R) v) g =
      -cellInner G k f (fun R => (fderiv ℝ g R) v) := by
  have hc : ContDiff ℝ 1 (fun R => conj (f R) * g R) :=
    (Complex.conjCLE.contDiff.comp hf).mul hg
  have hz := periodic_cell_integral_direction_zero G k _ hc
    (dual_cross_periodic G theta k f g hfb hgb) v
  have hd (R : ℂ) : (fderiv ℝ (fun R => conj (f R) * g R) R) v =
      conj ((fderiv ℝ f R) v) * g R + conj (f R) * (fderiv ℝ g R) v := by
    have h := ((Complex.conjCLE.hasFDerivAt.comp R
      ((hf.differentiable one_ne_zero) R).hasFDerivAt).mul
      ((hg.differentiable one_ne_zero) R).hasFDerivAt).fderiv
    have hv := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) h
    simpa only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, Pi.mul_def, Function.comp_def, smul_eq_mul, add_comm, mul_comm] using hv
  simp_rw [hd] at hz
  rw [integral_add
    (cellInner_integrable G k _ _ ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const) hg.continuous)
    (cellInner_integrable G k _ _ hf.continuous ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const))] at hz
  exact eq_neg_of_add_eq_zero_left hz

theorem parameterWirtinger_continuous (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) :
    Continuous (parameterWirtinger f) := by
  unfold parameterWirtinger
  exact (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
    (continuous_const.mul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const))).div_const 2

theorem parameterWirtingerBar_continuous (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) :
    Continuous (parameterWirtingerBar f) := by
  unfold parameterWirtingerBar
  exact (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
    (continuous_const.mul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const))).div_const 2

/-- Actual Wirtinger integration by parts, including the conjugation of
its imaginary coefficient in the first slot of the physical cell inner product. -/
theorem dual_cell_wirtinger_integrationByParts (G : Geometry) (theta : Twist) (k : ℕ)
    (f g : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfb : HasDualBoundary G theta k f) (hgb : HasDualBoundary G theta k g) :
    cellInner G k (parameterWirtinger f) g =
      -cellInner G k f (parameterWirtingerBar g) := by
  have heF : parameterWirtinger f =
      (1/2 : ℂ) • (fun R => (fderiv ℝ f R) 1) +
      (-Complex.I/2) • (fun R => (fderiv ℝ f R) Complex.I) := by
    funext R
    simp only [parameterWirtinger, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heG : parameterWirtingerBar g =
      (1/2 : ℂ) • (fun R => (fderiv ℝ g R) 1) +
      (Complex.I/2) • (fun R => (fderiv ℝ g R) Complex.I) := by
    funext R
    simp only [parameterWirtingerBar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdf (v : ℂ) : Continuous (fun R => (fderiv ℝ f R) v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdg (v : ℂ) : Continuous (fun R => (fderiv ℝ g R) v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [heF, heG, cellInner_add_left G k _ _ _
    ((hdf 1).const_smul _) ((hdf Complex.I).const_smul _) hg.continuous,
    cellInner_add_right G k _ _ _ hf.continuous ((hdg 1).const_smul _)
      ((hdg Complex.I).const_smul _),
    cellInner_smul_left, cellInner_smul_left, cellInner_smul_right, cellInner_smul_right,
    dual_cell_direction_integrationByParts G theta k f g hf hg hfb hgb 1,
    dual_cell_direction_integrationByParts G theta k f g hf hg hfb hgb Complex.I]
  simp only [map_div₀, map_one, map_ofNat, map_neg, Complex.conj_I]
  ring

/-- The magnetic potential's conjugate is exactly the potential occurring
in the raising operator. This identity uses the original cell integral. -/
theorem cellInner_conj_coordinate (G : Geometry) (k : ℕ) (f g : ℂ → ℂ) :
    cellInner G k (fun R => conj R * f R) g =
      cellInner G k f (fun R => R * g R) := by
  unfold cellInner
  apply integral_congr_ae
  filter_upwards [] with R
  simp only [map_mul, Complex.conj_conj]
  ring

/-- The original parameter lowering and raising operators are adjoints
in the physical charge-k cell integral. This is on smooth dual parameter
sections, not on the finite physical LLL. -/
theorem parameterLower_adjoint (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (f g : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfb : HasDualBoundary G theta k f) (hgb : HasDualBoundary G theta k g) :
    cellInner G k (parameterLower k f) g = cellInner G k f (parameterRaise k g) := by
  have heF : parameterLower k f =
      -((Real.sqrt (k:ℝ):ℂ)⁻¹) •
        (parameterWirtinger f + ((k:ℂ)/2) • (fun R => conj R * f R)) := by
    funext R
    simp only [parameterLower, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have heG : parameterRaise k g =
      ((Real.sqrt (k:ℝ):ℂ)⁻¹) •
        (parameterWirtingerBar g + (-((k:ℂ)/2)) • (fun R => R * g R)) := by
    funext R
    simp only [parameterRaise, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have hcf : Continuous (fun R => conj R * f R) := Complex.continuous_conj.mul hf.continuous
  have hcg : Continuous (fun R => R * g R) := continuous_id.mul hg.continuous
  rw [heF, heG, cellInner_smul_left, cellInner_smul_right,
    cellInner_add_left G k _ _ _ (parameterWirtinger_continuous f hf)
      (hcf.const_smul _) hg.continuous,
    cellInner_add_right G k _ _ _ hf.continuous (parameterWirtingerBar_continuous g hg)
      (hcg.const_smul _), cellInner_smul_left, cellInner_smul_right,
    dual_cell_wirtinger_integrationByParts G theta k f g hf hg hfb hgb,
    cellInner_conj_coordinate]
  simp only [map_neg, map_inv₀, Complex.conj_ofReal, map_div₀, map_natCast, map_ofNat]
  ring

end TorusLean.Shared.ParameterCellAdjoint
