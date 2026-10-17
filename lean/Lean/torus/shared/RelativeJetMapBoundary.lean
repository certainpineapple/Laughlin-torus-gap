import torus.shared.RelativeJetMapAnalytic

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.NormalJetBridge
open scoped TensorProduct ComplexConjugate

/-- Both original magnetic boundary laws compose on the full tensor, with
exactly the sum charge and the original common twist. -/
theorem rawPairFunction_simultaneous_boundary (G : Geometry) (theta : Twist)
    (a b : ℕ) (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b)
    (p : ℤ × ℤ) (z : ℂ × ℂ) :
    Complex.exp (magneticExponent a z.1 (latticePeriod G.omega1 G.omega2 p)) *
      Complex.exp (magneticExponent b z.2 (latticePeriod G.omega1 G.omega2 p)) *
      rawPairFunction G theta a b ψ
        (z.1 - latticePeriod G.omega1 G.omega2 p,
          z.2 - latticePeriod G.omega1 G.omega2 p) =
    latticeChi G.M theta.theta1 theta.theta2 p ^ (a+b) *
      rawPairFunction G theta a b ψ z := by
  induction ψ using TensorProduct.induction_on with
  | zero => simp
  | add ψ φ hψ hφ =>
    simp only [map_add, Pi.add_apply, mul_add, hψ, hφ]
  | tmul f g =>
    have hf := congrFun (f.property.2 p) z.1
    have hg := congrFun (g.property.2 p) z.2
    simp only [magneticTranslate] at hf hg
    simp only [rawPairFunction_tmul_apply, pow_add]
    calc
      _ = (Complex.exp (magneticExponent a z.1 (latticePeriod G.omega1 G.omega2 p)) *
          f.val (z.1 - latticePeriod G.omega1 G.omega2 p)) *
        (Complex.exp (magneticExponent b z.2 (latticePeriod G.omega1 G.omega2 p)) *
          g.val (z.2 - latticePeriod G.omega1 G.omega2 p)) := by ring
      _ = _ := by rw [hf, hg]; ring

/-- The simultaneous magnetic multiplier is independent of the relative
coordinate. This cancellation preserves all lattice periods. -/
theorem jacobi_simultaneous_magneticExponent (a b : ℝ) (hab : a+b ≠ 0)
    (C r x : ℂ) :
    magneticExponent a (jacobiFirst a b C r) x +
      magneticExponent b (jacobiSecond a b C r) x =
        magneticExponent (a+b) C x := by
  have heq : ((a : ℂ) * x + (b : ℂ) * x) / ((a+b : ℝ) : ℂ) = x := by
    have habc : (a : ℂ) + (b : ℂ) ≠ 0 := by
      simpa only [← Complex.ofReal_add, Complex.ofReal_ne_zero] using hab
    push_cast
    field_simp
    <;> ring
  rw [jacobi_magneticExponent a b hab, heq]
  simp [magneticExponent]

/-- Exact all-period magnetic law of the original covariant jet. The
relative derivative commutes with the now constant magnetic multiplier. -/
theorem rawPairFunction_normalJet_boundary (G : Geometry) (theta : Twist)
    (a b : ℕ) (hab : (a:ℝ)+(b:ℝ) ≠ 0) (d : ℕ)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) :
    HasLatticeBoundary G.M (a+b) G.omega1 G.omega2 theta.theta1 theta.theta2
      (localNormalJet a b d (rawPairFunction G theta a b ψ)) := by
  intro p
  funext C
  let x := latticePeriod G.omega1 G.omega2 p
  let χ := latticeChi G.M theta.theta1 theta.theta2 p ^ (a+b)
  let m := Complex.exp (magneticExponent ((a:ℝ)+(b:ℝ)) C x)
  let H := fun (D r : ℂ) => Complex.exp ((relativeCharge a b : ℂ) * (r * conj r) / 2) *
    rawPairFunction G theta a b ψ (jacobiFirst a b D r, jacobiSecond a b D r)
  have hfun : (fun r => m * H (C-x) r) = (fun r => χ * H C r) := by
    funext r
    have hbnd := rawPairFunction_simultaneous_boundary G theta a b ψ p
      (jacobiFirst a b C r, jacobiSecond a b C r)
    rw [← Complex.exp_add, jacobi_simultaneous_magneticExponent (a:ℝ) (b:ℝ) hab] at hbnd
    have hfirst : jacobiFirst a b (C-x) r = jacobiFirst a b C r - x := by
      unfold jacobiFirst; ring
    have hsecond : jacobiSecond a b (C-x) r = jacobiSecond a b C r - x := by
      unfold jacobiSecond; ring
    dsimp only [H]
    rw [hfirst, hsecond]
    change m * (_ * _) = χ * (_ * _)
    calc
      _ = Complex.exp ((relativeCharge a b : ℂ) * (r * conj r) / 2) *
        (m * rawPairFunction G theta a b ψ
          (jacobiFirst a b C r - x, jacobiSecond a b C r - x)) := by ring
      _ = _ := by rw [hbnd]; ring
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv d f 0) hfun
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field] at hd
  change Complex.exp (magneticExponent ((a+b : ℕ):ℝ) C x) *
    ((jetScale a b d)⁻¹ * iteratedDeriv d (H (C-x)) 0) =
    χ * ((jetScale a b d)⁻¹ * iteratedDeriv d (H C) 0)
  rw [Nat.cast_add]
  change m * (_ * _) = χ * (_ * _)
  calc
    _ = (jetScale a b d)⁻¹ * (m * iteratedDeriv d (H (C-x)) 0) := by ring
    _ = _ := by rw [hd]; ring

end TorusLean.Shared.RelativeJetMap
