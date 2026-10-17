import torus.shared.ParameterRawJetLadderCalculus

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterLadderProduct
open TorusLean.Geometry TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.ParameterRawJetLadder
open scoped ComplexConjugate

theorem parameterLower_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a+b)]
    (f g : ℂ → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (R : ℂ) :
    (Real.sqrt ((a+b:ℕ):ℝ):ℂ) * parameterLower (a+b) (fun z => f z*g z) R =
      (Real.sqrt (a:ℝ):ℂ) * parameterLower a f R * g R +
      (Real.sqrt (b:ℝ):ℂ) * f R * parameterLower b g R := by
  have ha : (Real.sqrt (a:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne a)))))
  have hb : (Real.sqrt (b:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne b)))))
  have hab : (Real.sqrt ((a+b:ℕ):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (a+b))))))
  unfold parameterLower
  rw [wirtinger_mul f g hf hg R]
  field_simp [ha, hb, hab]
  push_cast
  ring

theorem parameterRaise_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a+b)]
    (f g : ℂ → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (R : ℂ) :
    (Real.sqrt ((a+b:ℕ):ℝ):ℂ) * parameterRaise (a+b) (fun z => f z*g z) R =
      (Real.sqrt (a:ℝ):ℂ) * parameterRaise a f R * g R +
      (Real.sqrt (b:ℝ):ℂ) * f R * parameterRaise b g R := by
  have ha : (Real.sqrt (a:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne a)))))
  have hb : (Real.sqrt (b:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne b)))))
  have hab : (Real.sqrt ((a+b:ℕ):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (a+b))))))
  unfold parameterRaise
  rw [wirtingerBar_mul f g hf hg R]
  field_simp [ha, hb, hab]
  push_cast
  ring

/-- Multiplication retains exactly the original common twist and adds charge. -/
theorem hasDualBoundary_mul (G : Geometry) (theta : Twist) (a b : ℕ)
    (f g : ℂ → ℂ) (hf : HasDualBoundary G theta a f) (hg : HasDualBoundary G theta b g) :
    HasDualBoundary G theta (a+b) (fun z => f z*g z) := by
  intro p
  funext z
  have hfp := congrFun (hf p) z
  have hgp := congrFun (hg p) z
  simp only [magneticTranslate] at hfp hgp ⊢
  have he : magneticExponent ((a+b:ℕ):ℝ) z (latticePeriod G.omega1 G.omega2 p) =
      magneticExponent a z (latticePeriod G.omega1 G.omega2 p) +
      magneticExponent b z (latticePeriod G.omega1 G.omega2 p) := by
    unfold magneticExponent
    push_cast
    ring
  rw [he, Complex.exp_add, map_mul, map_mul, pow_add]
  calc
    _ = (Complex.exp (magneticExponent a z (latticePeriod G.omega1 G.omega2 p))*conj (f (z-latticePeriod G.omega1 G.omega2 p))) *
      (Complex.exp (magneticExponent b z (latticePeriod G.omega1 G.omega2 p))*conj (g (z-latticePeriod G.omega1 G.omega2 p))) := by ring
    _ = _ := by rw [hfp,hgp]; ring

end TorusLean.Shared.ParameterLadderProduct
