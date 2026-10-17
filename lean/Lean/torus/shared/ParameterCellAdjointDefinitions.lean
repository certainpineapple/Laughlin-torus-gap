import torus.shared.CellMeasure
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Actual universal-cover parameter derivatives and the dual of the original
magnetic boundary law. No finite physical LLL carrier is introduced. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterCellAdjoint
open scoped ComplexConjugate

/-- Dual parameter sections have exactly the conjugate of the original
charge-k, same-twist magnetic boundary law. -/
def HasDualBoundary (G : Geometry) (theta : Twist) (k : ℕ) (f : ℂ → ℂ) : Prop :=
  TorusLean.Geometry.HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2
    (fun R => conj (f R))

/-- The genuine real-Frechet Wirtinger derivative ∂R. -/
def parameterWirtinger (f : ℂ → ℂ) (R : ℂ) : ℂ :=
  ((fderiv ℝ f R) 1 - Complex.I * (fderiv ℝ f R) Complex.I) / 2

/-- The genuine real-Frechet Wirtinger derivative ∂barR. -/
def parameterWirtingerBar (f : ℂ → ℂ) (R : ℂ) : ℂ :=
  ((fderiv ℝ f R) 1 + Complex.I * (fderiv ℝ f R) Complex.I) / 2

/-- The paper's lowering operator on dual parameter sections. -/
def parameterLower (k : ℕ) (f : ℂ → ℂ) (R : ℂ) : ℂ :=
  -(parameterWirtinger f R + ((k : ℂ)/2) * conj R * f R) /
    (Real.sqrt (k : ℝ) : ℂ)

/-- The paper's raising operator on dual parameter sections. -/
def parameterRaise (k : ℕ) (f : ℂ → ℂ) (R : ℂ) : ℂ :=
  (parameterWirtingerBar f R - ((k : ℂ)/2) * R * f R) /
    (Real.sqrt (k : ℝ) : ℂ)

end TorusLean.Shared.ParameterCellAdjoint
