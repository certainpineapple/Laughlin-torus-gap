import torus.geometry.MagneticTranslation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Lattice phases for the fixed magnetic convention

Source: `sections/02-geometry.tex`, the semicharacter immediately following
`eq:translation`. Coordinates are actual integer lattice vectors. Flux is a
natural number; the geometric area identity is always an explicit hypothesis.
No lattice discreteness, systole estimate, or LLL dimension is assumed.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

open scoped ComplexConjugate

noncomputable section

/-- Universal-cover lattice vector, in the ordered basis from the paper. -/
def latticePeriod (omega1 omega2 : ℂ) (p : ℤ × ℤ) : ℂ :=
  (p.1 : ℂ) * omega1 + (p.2 : ℂ) * omega2

/-- Signed area of the ordered lattice basis. -/
def latticeArea (omega1 omega2 : ℂ) : ℝ := (conj omega1 * omega2).im

/-- The semicharacter exponent includes the integer-flux parity term. -/
def twistExponent (M : ℕ) (theta1 theta2 : ℝ) (p : ℤ × ℤ) : ℂ :=
  (((p.1 : ℝ) * theta1 + (p.2 : ℝ) * theta2 +
      Real.pi * (M : ℝ) * (p.1 : ℝ) * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I

/-- The paper's `chi`, with negative lattice indices allowed. -/
def latticeChi (M : ℕ) (theta1 theta2 : ℝ) (p : ℤ × ℤ) : ℂ :=
  Complex.exp (twistExponent M theta1 theta2 p)

theorem latticePeriod_add (omega1 omega2 : ℂ) (p q : ℤ × ℤ) :
    latticePeriod omega1 omega2 (p + q) =
      latticePeriod omega1 omega2 p + latticePeriod omega1 omega2 q := by
  simp only [latticePeriod, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem latticePeriod_zero (omega1 omega2 : ℂ) :
    latticePeriod omega1 omega2 (0, 0) = 0 := by
  simp [latticePeriod]

theorem lattice_symplectic (omega1 omega2 : ℂ) (p q : ℤ × ℤ) :
    (latticePeriod omega1 omega2 p * conj (latticePeriod omega1 omega2 q)).im =
      (((p.2 * q.1 - p.1 * q.2 : ℤ) : ℝ)) * latticeArea omega1 omega2 := by
  simp [latticePeriod, latticeArea, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, map_add, map_mul]
  ring

theorem latticeChi_ne_zero (M : ℕ) (theta1 theta2 : ℝ) (p : ℤ × ℤ) :
    latticeChi M theta1 theta2 p ≠ 0 :=
  Complex.exp_ne_zero _

theorem latticeChi_norm (M : ℕ) (theta1 theta2 : ℝ) (p : ℤ × ℤ) :
    ‖latticeChi M theta1 theta2 p‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- This checks that the exponential definition is exactly
`exp(i*(m*theta1+n*theta2))*(-1)^(M*m*n)`, not an ordinary character. -/
theorem latticeChi_eq_paper (M : ℕ) (theta1 theta2 : ℝ) (p : ℤ × ℤ) :
    latticeChi M theta1 theta2 p =
      Complex.exp (((((p.1 : ℝ) * theta1 + (p.2 : ℝ) * theta2) : ℝ) : ℂ) *
        Complex.I) * (-1 : ℂ) ^ ((M : ℤ) * p.1 * p.2) := by
  have he : twistExponent M theta1 theta2 p =
      (((((p.1 : ℝ) * theta1 + (p.2 : ℝ) * theta2) : ℝ) : ℂ) * Complex.I) +
        (((M : ℤ) * p.1 * p.2 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    simp only [twistExponent, Complex.ofReal_add, Complex.ofReal_mul,
      Int.cast_mul, Int.cast_natCast, Complex.ofReal_intCast, Complex.ofReal_natCast]
    ring
  rw [latticeChi, he, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem latticeCocycle_eq_flux (M : ℕ) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) (p q : ℤ × ℤ) :
    magneticCocycle 1 (latticePeriod omega1 omega2 p) (latticePeriod omega1 omega2 q) =
      Complex.exp (((M : ℤ) * (p.1 * q.2 - p.2 * q.1) : ℤ) *
        ((Real.pi : ℂ) * Complex.I)) := by
  rw [magneticCocycle_eq_im, lattice_symplectic, harea]
  congr 1
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_intCast,
    Complex.ofReal_natCast, Complex.ofReal_one]
  ring

/-- Semicharacter law, proved from actual integer flux and the area identity. -/
theorem latticeChi_semicharacter (M : ℕ) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (theta1 theta2 : ℝ) (p q : ℤ × ℤ) :
    latticeChi M theta1 theta2 p * latticeChi M theta1 theta2 q =
      magneticCocycle 1 (latticePeriod omega1 omega2 p) (latticePeriod omega1 omega2 q) *
        latticeChi M theta1 theta2 (p + q) := by
  have he : twistExponent M theta1 theta2 p + twistExponent M theta1 theta2 q =
      (((M : ℤ) * (p.1 * q.2 - p.2 * q.1) : ℤ) : ℂ) *
          ((Real.pi : ℂ) * Complex.I) + twistExponent M theta1 theta2 (p + q) +
        (((-(M : ℤ) * p.1 * q.2 : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)) := by
    simp only [twistExponent, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_mul,
      Int.cast_sub, Int.cast_neg, Int.cast_natCast, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]
    ring
  rw [latticeCocycle_eq_flux M omega1 omega2 harea]
  simp only [latticeChi, ← Complex.exp_add]
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Integer flux makes lattice translations commute, although the
individual cocycle can equal minus one. -/
theorem latticeCocycle_symmetric (M : ℕ) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) (p q : ℤ × ℤ) :
    magneticCocycle 1 (latticePeriod omega1 omega2 p) (latticePeriod omega1 omega2 q) =
      magneticCocycle 1 (latticePeriod omega1 omega2 q) (latticePeriod omega1 omega2 p) := by
  rw [latticeCocycle_eq_flux M omega1 omega2 harea,
    latticeCocycle_eq_flux M omega1 omega2 harea]
  have hn : (M : ℤ) * (q.1 * p.2 - q.2 * p.1) =
      -((M : ℤ) * (p.1 * q.2 - p.2 * q.1)) := by ring
  rw [hn]
  let n : ℤ := (M : ℤ) * (p.1 * q.2 - p.2 * q.1)
  change Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) =
    Complex.exp (((-n : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I))
  calc
    _ = Complex.exp (((-n : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      congr 1
      simp only [Int.cast_neg]
      ring
    _ = _ := by rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The fractional translation in `eq:exact-JJ` has trivial commutator
with every lattice period on charge `t`; integrality of `a` is essential. -/
theorem fractionalLattice_cocycle_symmetric (M a t : ℕ) (ht : 0 < t)
    (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) (p q : ℤ × ℤ) :
    magneticCocycle (t : ℝ) (latticePeriod omega1 omega2 p)
        ((((a : ℝ) / (t : ℝ) : ℝ) : ℂ) * latticePeriod omega1 omega2 q) =
      magneticCocycle (t : ℝ)
        ((((a : ℝ) / (t : ℝ) : ℝ) : ℂ) * latticePeriod omega1 omega2 q)
        (latticePeriod omega1 omega2 p) := by
  have htn : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hscale : (t : ℝ) * ((a : ℝ) / (t : ℝ)) = (a : ℝ) := by
    rw [mul_div_cancel₀ _ htn]
  rw [magneticCocycle_scale_right, magneticCocycle_scale_left, hscale,
    magneticCocycle_nat_charge, magneticCocycle_nat_charge,
    latticeCocycle_symmetric M omega1 omega2 harea]

#print axioms latticePeriod_add
#print axioms latticePeriod_zero
#print axioms lattice_symplectic
#print axioms latticeChi_ne_zero
#print axioms latticeChi_norm
#print axioms latticeChi_eq_paper
#print axioms latticeCocycle_eq_flux
#print axioms latticeChi_semicharacter
#print axioms latticeCocycle_symmetric
#print axioms fractionalLattice_cocycle_symmetric

end

end TorusLean.Geometry
