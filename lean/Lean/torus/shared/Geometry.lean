import torus.geometry.MagneticSections
import torus.shared.Inputs

/-! Shared physical inputs. No dimension, frame, kernel, or gap is an input. -/

set_option autoImplicit false

namespace TorusLean.Shared

open scoped ComplexConjugate

noncomputable def period (G : Geometry) (p : ℤ × ℤ) : ℂ :=
  TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p

noncomputable def chi (G : Geometry) (theta : Twist) (p : ℤ × ℤ) : ℂ :=
  TorusLean.Geometry.latticeChi G.M theta.theta1 theta.theta2 p

/-- Actual Gaussian-holomorphic magnetic sections. The cell Hilbert structure
and dimension theorem are pending, so this is the raw section type. -/
def RawLLL (G : Geometry) (theta : Twist) (k : ℕ) :=
  TorusLean.Geometry.RawLLL G.M k G.omega1 G.omega2 theta.theta1 theta.theta2

/-- Every relative component retains the whole COM section space. -/
def FullCOMTarget (G : Geometry) (theta : Twist) (a b : ℕ) (D : Finset ℕ) :=
  TorusLean.Geometry.FullCOMTarget D G.M a b G.omega1 G.omega2
    theta.theta1 theta.theta2

end TorusLean.Shared
