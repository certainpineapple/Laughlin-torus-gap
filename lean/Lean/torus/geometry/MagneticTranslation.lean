import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring

/-!
# Magnetic translation on actual complex-valued sections

Source: the frozen paper, `sections/02-geometry.tex`, `eq:translation`.
The real charge includes the positive nonintegral relative oscillator charge;
physical torus charges will be positive integers. No Hilbert space, dimension,
unitarity with respect to a cell integral, or convergence claim is assumed here.
The eigencharacter has the paper's direction: `T_lambda f = chi_lambda * f`.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

open scoped ComplexConjugate

noncomputable section

/-- Exponent in the paper's magnetic translation convention. -/
def magneticExponent (k : ℝ) (z x : ℂ) : ℂ :=
  (k : ℂ) * (z * conj x - conj z * x) / 2

/-- Translation on actual functions on the universal cover. -/
def magneticTranslate (k : ℝ) (x : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (magneticExponent k z x) * f (z - x)

/-- Projective multiplier, written without an implicit sign convention. -/
def magneticCocycle (k : ℝ) (x y : ℂ) : ℂ :=
  Complex.exp ((k : ℂ) * (conj x * y - x * conj y) / 2)

theorem magneticExponent_comp (k : ℝ) (z x y : ℂ) :
    magneticExponent k z x + magneticExponent k (z - x) y =
      (k : ℂ) * (conj x * y - x * conj y) / 2 +
        magneticExponent k z (x + y) := by
  simp only [magneticExponent, map_sub, map_add]
  ring

theorem magneticTranslate_comp (k : ℝ) (x y : ℂ) (f : ℂ → ℂ) :
    magneticTranslate k x (magneticTranslate k y f) =
      fun z => magneticCocycle k x y * magneticTranslate k (x + y) f z := by
  funext z
  simp only [magneticTranslate, magneticCocycle]
  rw [← mul_assoc, ← Complex.exp_add, magneticExponent_comp, Complex.exp_add]
  have hsub : z - x - y = z - (x + y) := by ring
  rw [hsub, mul_assoc]

theorem magneticTranslate_zero (k : ℝ) (f : ℂ → ℂ) :
    magneticTranslate k 0 f = f := by
  funext z
  simp [magneticTranslate, magneticExponent]

theorem magneticCocycle_neg_self (k : ℝ) (x : ℂ) :
    magneticCocycle k x (-x) = 1 := by
  simp [magneticCocycle, map_neg, mul_comm]

theorem magneticTranslate_inverse (k : ℝ) (x : ℂ) (f : ℂ → ℂ) :
    magneticTranslate k x (magneticTranslate k (-x) f) = f := by
  rw [magneticTranslate_comp, magneticCocycle_neg_self]
  simp only [add_neg_cancel, one_mul]
  exact magneticTranslate_zero k f

theorem magneticExponent_add_period (k : ℝ) (z x : ℂ) :
    magneticExponent k (z + x) x = magneticExponent k z x := by
  simp only [magneticExponent, map_add]
  ring

theorem magneticExponent_eq_im (k : ℝ) (z x : ℂ) :
    magneticExponent k z x = ((k * (z * conj x).im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [magneticExponent, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im] <;>
    ring

/-- The projective phase is exactly the sign printed in `eq:translation`. -/
theorem magneticCocycle_eq_im (k : ℝ) (x y : ℂ) :
    magneticCocycle k x y =
      Complex.exp (((-k * (x * conj y).im : ℝ) : ℂ) * Complex.I) := by
  unfold magneticCocycle
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im] <;>
    ring

theorem magneticMultiplier_norm (k : ℝ) (z x : ℂ) :
    ‖Complex.exp (magneticExponent k z x)‖ = 1 := by
  rw [magneticExponent_eq_im, Complex.norm_exp_ofReal_mul_I]

/-- Pointwise norm preservation after translating the argument.
This is not yet cell-inner-product unitarity. -/
theorem magneticTranslate_norm (k : ℝ) (x z : ℂ) (f : ℂ → ℂ) :
    ‖magneticTranslate k x f z‖ = ‖f (z - x)‖ := by
  simp only [magneticTranslate, Complex.norm_mul, magneticMultiplier_norm, one_mul]

theorem magneticTranslate_const_mul (k : ℝ) (x c : ℂ) (f : ℂ → ℂ) :
    magneticTranslate k x (fun z => c * f z) =
      fun z => c * magneticTranslate k x f z := by
  funext z
  simp only [magneticTranslate]
  ring

theorem magneticCocycle_scale_right (k r : ℝ) (x y : ℂ) :
    magneticCocycle k x ((r : ℂ) * y) = magneticCocycle (k * r) x y := by
  unfold magneticCocycle
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

theorem magneticCocycle_scale_left (k r : ℝ) (x y : ℂ) :
    magneticCocycle k ((r : ℂ) * x) y = magneticCocycle (k * r) x y := by
  unfold magneticCocycle
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

theorem magneticCocycle_nat_charge (k : ℕ) (x y : ℂ) :
    magneticCocycle (k : ℝ) x y = magneticCocycle 1 x y ^ k := by
  unfold magneticCocycle
  rw [← Complex.exp_nat_mul]
  congr 1
  simp only [Complex.ofReal_natCast, Complex.ofReal_one]
  ring

/-- Explicit local criterion; integral flux instantiates it in LatticePhase.
No commutativity of arbitrary magnetic translations is assumed. -/
theorem magneticTranslate_comm_of_cocycle (k : ℝ) (x y : ℂ)
    (hphase : magneticCocycle k x y = magneticCocycle k y x) (f : ℂ → ℂ) :
    magneticTranslate k x (magneticTranslate k y f) =
      magneticTranslate k y (magneticTranslate k x f) := by
  rw [magneticTranslate_comp, magneticTranslate_comp, hphase, add_comm x y]

/-- A single-period eigencharacter law. The multiplier is not inverted here. -/
def HasMagneticEigencharacter (k : ℝ) (x c : ℂ) (f : ℂ → ℂ) : Prop :=
  magneticTranslate k x f = fun z => c * f z

/-- The positive-direction boundary law has the inverse eigencharacter. -/
theorem magneticEigencharacter_iff_forward (k : ℝ) (x c : ℂ)
    (hc : c ≠ 0) (f : ℂ → ℂ) :
    HasMagneticEigencharacter k x c f ↔
      ∀ z, f (z + x) = c⁻¹ * Complex.exp (magneticExponent k z x) * f z := by
  constructor
  · intro h z
    have hz := congrFun h (z + x)
    change Complex.exp (magneticExponent k (z + x) x) * f (z + x - x) =
      c * f (z + x) at hz
    rw [magneticExponent_add_period, add_sub_cancel_right] at hz
    calc
      f (z + x) = c⁻¹ * (c * f (z + x)) := by simp [hc]
      _ = c⁻¹ * (Complex.exp (magneticExponent k z x) * f z) := by rw [hz]
      _ = _ := by ring
  · intro h
    funext z
    change Complex.exp (magneticExponent k z x) * f (z - x) = c * f z
    have hz := h (z - x)
    have he : magneticExponent k (z - x) x = magneticExponent k z x := by
      have h := magneticExponent_add_period k (z - x) x
      simpa only [sub_add_cancel] using h.symm
    rw [sub_add_cancel, he] at hz
    rw [hz]
    simp [hc, mul_assoc]

/-- Preservation of one boundary condition with the commutator phase explicit. -/
theorem magneticEigencharacter_translate (k : ℝ) (lambda x c : ℂ) (f : ℂ → ℂ)
    (hphase : magneticCocycle k lambda x = magneticCocycle k x lambda)
    (hf : HasMagneticEigencharacter k lambda c f) :
    HasMagneticEigencharacter k lambda c (magneticTranslate k x f) := by
  unfold HasMagneticEigencharacter at hf ⊢
  rw [magneticTranslate_comm_of_cocycle k lambda x hphase, hf,
    magneticTranslate_const_mul]

#print axioms magneticExponent_comp
#print axioms magneticTranslate_comp
#print axioms magneticTranslate_zero
#print axioms magneticCocycle_neg_self
#print axioms magneticTranslate_inverse
#print axioms magneticExponent_add_period
#print axioms magneticExponent_eq_im
#print axioms magneticCocycle_eq_im
#print axioms magneticMultiplier_norm
#print axioms magneticTranslate_norm
#print axioms magneticTranslate_const_mul
#print axioms magneticCocycle_scale_right
#print axioms magneticCocycle_scale_left
#print axioms magneticCocycle_nat_charge
#print axioms magneticTranslate_comm_of_cocycle
#print axioms magneticEigencharacter_iff_forward
#print axioms magneticEigencharacter_translate

end

end TorusLean.Geometry
