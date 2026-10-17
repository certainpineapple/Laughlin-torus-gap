import torus.geometry.MagneticSections
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.FieldSimp

/-!
# Local Jacobi coordinates and the actual normal-jet formula

Source: `sections/02-geometry.tex`, `eq:J-definition` and the two splitting
identities in the proof of `lem:relative-frame`. These are local identities
on the universal cover, not a global tensor factorization of torus spaces.
The jet's RawLLL mapping, adjoint, and Gram expansion remain pending.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

open scoped ComplexConjugate

noncomputable section

def relativeCharge (a b : ℝ) : ℝ := a * b / (a + b)

def jacobiFirst (a b : ℝ) (C r : ℂ) : ℂ :=
  C + ((b / (a + b) : ℝ) : ℂ) * r

def jacobiSecond (a b : ℝ) (C r : ℂ) : ℂ :=
  C - ((a / (a + b) : ℝ) : ℂ) * r

/-- Original local covariant normal-jet formula. Its codomain is an actual
function, until the full-space mapping theorem is proved. -/
def localNormalJet (a b : ℝ) (d : ℕ) (F : ℂ × ℂ → ℂ) : ℂ → ℂ :=
  fun C => (Real.sqrt (relativeCharge a b ^ d * (d.factorial : ℝ)) : ℂ)⁻¹ *
    iteratedDeriv d (fun r : ℂ =>
      Complex.exp ((relativeCharge a b : ℂ) * (r * conj r) / 2) *
        F (jacobiFirst a b C r, jacobiSecond a b C r)) 0

theorem relativeCharge_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < relativeCharge a b :=
  div_pos (mul_pos ha hb) (add_pos ha hb)

theorem jacobi_gaussian_quadratic (a b : ℝ) (hab : a + b ≠ 0) (C r : ℂ) :
    (a : ℂ) * (jacobiFirst a b C r * conj (jacobiFirst a b C r)) +
      (b : ℂ) * (jacobiSecond a b C r * conj (jacobiSecond a b C r)) =
      ((a + b : ℝ) : ℂ) * (C * conj C) +
        (relativeCharge a b : ℂ) * (r * conj r) := by
  have habc : (a : ℂ) + (b : ℂ) ≠ 0 := by
    simpa only [← Complex.ofReal_add, Complex.ofReal_ne_zero] using hab
  simp only [jacobiFirst, jacobiSecond, relativeCharge, map_add, map_sub, map_mul,
    Complex.conj_ofReal]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp [habc]
  ring

/-- The physical Gaussian precisely separates under this weighted local
change of coordinates; the relative factor is not another torus flux. -/
theorem jacobi_gaussian_product (a b : ℝ) (hab : a + b ≠ 0) (C r : ℂ) :
    gaussianFactor a (jacobiFirst a b C r) *
      gaussianFactor b (jacobiSecond a b C r) =
      gaussianFactor (a + b) C * gaussianFactor (relativeCharge a b) r := by
  simp only [gaussianFactor, ← Complex.exp_add]
  congr 1
  have hq := jacobi_gaussian_quadratic a b hab C r
  calc
    _ = -((a : ℂ) * (jacobiFirst a b C r * conj (jacobiFirst a b C r)) +
        (b : ℂ) * (jacobiSecond a b C r * conj (jacobiSecond a b C r))) / 2 := by ring
    _ = _ := by rw [hq]; ring

theorem jacobi_covariant_gaussian_cancel (a b : ℝ) (hab : a + b ≠ 0) (C r : ℂ) :
    Complex.exp ((relativeCharge a b : ℂ) * (r * conj r) / 2) *
      (gaussianFactor a (jacobiFirst a b C r) *
        gaussianFactor b (jacobiSecond a b C r)) = gaussianFactor (a + b) C := by
  rw [jacobi_gaussian_product a b hab]
  unfold gaussianFactor
  rw [mul_left_comm, ← Complex.exp_add]
  have hz : (relativeCharge a b : ℂ) * (r * conj r) / 2 +
      -(relativeCharge a b : ℂ) * (r * conj r) / 2 = 0 := by ring
  rw [hz, Complex.exp_zero, mul_one]

/-- Exact split of the magnetic bilinear form, including its phases. -/
theorem jacobi_magneticExponent (a b : ℝ) (hab : a + b ≠ 0) (C r x y : ℂ) :
    magneticExponent a (jacobiFirst a b C r) x +
      magneticExponent b (jacobiSecond a b C r) y =
      magneticExponent (a + b) C
        (((a : ℂ) * x + (b : ℂ) * y) / ((a + b : ℝ) : ℂ)) +
      magneticExponent (relativeCharge a b) r (x - y) := by
  have habc : (a : ℂ) + (b : ℂ) ≠ 0 := by
    simpa only [← Complex.ofReal_add, Complex.ofReal_ne_zero] using hab
  simp only [magneticExponent, jacobiFirst, jacobiSecond, relativeCharge, map_add,
    map_sub, map_mul, map_div₀, Complex.conj_ofReal]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp [habc]
  ring

theorem jacobi_magneticMultiplier (a b : ℝ) (hab : a + b ≠ 0) (C r x y : ℂ) :
    Complex.exp (magneticExponent a (jacobiFirst a b C r) x) *
      Complex.exp (magneticExponent b (jacobiSecond a b C r) y) =
      Complex.exp (magneticExponent (a + b) C
        (((a : ℂ) * x + (b : ℂ) * y) / ((a + b : ℝ) : ℂ))) *
      Complex.exp (magneticExponent (relativeCharge a b) r (x - y)) := by
  rw [← Complex.exp_add, jacobi_magneticExponent a b hab, Complex.exp_add]

#print axioms relativeCharge_pos
#print axioms jacobi_gaussian_quadratic
#print axioms jacobi_gaussian_product
#print axioms jacobi_covariant_gaussian_cancel
#print axioms jacobi_magneticExponent
#print axioms jacobi_magneticMultiplier

end

end TorusLean.Geometry
