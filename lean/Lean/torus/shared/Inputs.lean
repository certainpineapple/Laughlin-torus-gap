import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Stable physical inputs for parallel consumers; no dimension or gap fields. -/

set_option autoImplicit false

namespace TorusLean.Shared

open scoped ComplexConjugate

structure Geometry where
  M : ℕ
  flux_pos : 0 < M
  omega1 : ℂ
  omega2 : ℂ
  area : (conj omega1 * omega2).im = Real.pi * (M : ℝ)

structure Twist where
  theta1 : ℝ
  theta2 : ℝ

end TorusLean.Shared
