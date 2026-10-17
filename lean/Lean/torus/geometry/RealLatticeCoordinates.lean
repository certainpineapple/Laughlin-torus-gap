import torus.geometry.LatticeInjectivity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Actual real coordinate inverse and period basis

The two real coordinates parametrize the complex universal cover, not the
physical LLL. The inverse is obtained from the actual magnetic area. The
physical inputs remain positive natural flux and the explicit area equation.
The resulting real basis will induce the discrete integer lattice by ZSpan.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

open scoped ComplexConjugate

noncomputable section

def latticeRealPeriod (omega1 omega2 : ℂ) (u : Fin 2 → ℝ) : ℂ :=
  (u 0 : ℂ) * omega1 + (u 1 : ℂ) * omega2

def latticeCoordinate1 (omega1 omega2 z : ℂ) : ℝ :=
  (conj z * omega2).im / latticeArea omega1 omega2

def latticeCoordinate2 (omega1 omega2 z : ℂ) : ℝ :=
  (conj omega1 * z).im / latticeArea omega1 omega2

def latticeRealCoordinates (omega1 omega2 z : ℂ) : Fin 2 → ℝ :=
  ![latticeCoordinate1 omega1 omega2 z, latticeCoordinate2 omega1 omega2 z]

theorem latticeCoordinate1_numerator (omega1 omega2 : ℂ) (u : Fin 2 → ℝ) :
    (conj (latticeRealPeriod omega1 omega2 u) * omega2).im =
      u 0 * latticeArea omega1 omega2 := by
  simp [latticeRealPeriod, latticeArea, map_add, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im]
  ring

theorem latticeCoordinate2_numerator (omega1 omega2 : ℂ) (u : Fin 2 → ℝ) :
    (conj omega1 * latticeRealPeriod omega1 omega2 u).im =
      u 1 * latticeArea omega1 omega2 := by
  simp [latticeRealPeriod, latticeArea, Complex.mul_re, Complex.mul_im]
  ring

theorem latticeRealCoordinates_left_inverse (M : ℕ) (hM : 0 < M)
    (omega1 omega2 : ℂ) (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (u : Fin 2 → ℝ) :
    latticeRealCoordinates omega1 omega2 (latticeRealPeriod omega1 omega2 u) = u := by
  have hA : latticeArea omega1 omega2 ≠ 0 :=
    ne_of_gt (latticeArea_pos M hM omega1 omega2 harea)
  funext i
  fin_cases i
  · change (conj (latticeRealPeriod omega1 omega2 u) * omega2).im /
      latticeArea omega1 omega2 = u 0
    rw [latticeCoordinate1_numerator]
    exact mul_div_cancel_right₀ (u 0) hA
  · change (conj omega1 * latticeRealPeriod omega1 omega2 u).im /
      latticeArea omega1 omega2 = u 1
    rw [latticeCoordinate2_numerator]
    exact mul_div_cancel_right₀ (u 1) hA

theorem latticeRealCoordinates_right_inverse (M : ℕ) (hM : 0 < M)
    (omega1 omega2 : ℂ) (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (z : ℂ) :
    latticeRealPeriod omega1 omega2 (latticeRealCoordinates omega1 omega2 z) = z := by
  have hA : latticeArea omega1 omega2 ≠ 0 :=
    ne_of_gt (latticeArea_pos M hM omega1 omega2 harea)
  apply Complex.ext <;>
    simp [latticeRealPeriod, latticeRealCoordinates, latticeCoordinate1,
      latticeCoordinate2, Complex.mul_re, Complex.mul_im]
  all_goals
    field_simp [hA]
    simp only [latticeArea, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

/-- This equivalence is derived from legal geometry; invertibility is not an
extra field. It is the coordinate map of the actual complex plane. -/
def latticeRealEquiv (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ where
  toFun := latticeRealPeriod omega1 omega2
  invFun := latticeRealCoordinates omega1 omega2
  left_inv := latticeRealCoordinates_left_inverse M hM omega1 omega2 harea
  right_inv := latticeRealCoordinates_right_inverse M hM omega1 omega2 harea
  map_add' := by
    intro u v
    simp only [latticeRealPeriod, Pi.add_apply, Complex.ofReal_add]
    ring
  map_smul' := by
    intro c u
    simp only [RingHom.id_apply, latticeRealPeriod, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_mul]
    ring

def latticeRealBasis (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) : Module.Basis (Fin 2) ℝ ℂ :=
  (Pi.basisFun ℝ (Fin 2)).map (latticeRealEquiv M hM omega1 omega2 harea)

theorem latticeRealBasis_zero (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    latticeRealBasis M hM omega1 omega2 harea 0 = omega1 := by
  simp [latticeRealBasis, Module.Basis.map_apply, latticeRealEquiv, latticeRealPeriod,
    Pi.basisFun_apply]

theorem latticeRealBasis_one (M : ℕ) (hM : 0 < M) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ)) :
    latticeRealBasis M hM omega1 omega2 harea 1 = omega2 := by
  simp [latticeRealBasis, Module.Basis.map_apply, latticeRealEquiv, latticeRealPeriod,
    Pi.basisFun_apply]

#print axioms latticeCoordinate1_numerator
#print axioms latticeCoordinate2_numerator
#print axioms latticeRealCoordinates_left_inverse
#print axioms latticeRealCoordinates_right_inverse
#print axioms latticeRealBasis_zero
#print axioms latticeRealBasis_one

end

end TorusLean.Geometry
