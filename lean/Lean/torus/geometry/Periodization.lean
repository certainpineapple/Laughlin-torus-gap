import torus.geometry.MagneticSections
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Actual magnetic image series

Source: `sections/02-geometry.tex`, `eq:periodization`.
`tsum` is total, including for a nonsummable family. The analytic claim that
Gaussian-polynomial images converge absolutely and locally uniformly, and
that differentiated images may be summed, is NOT proved or assumed here.
`HasAbsolutelySummableImages` records that pending domain obligation openly.
The algebraic boundary law follows by exact reindexing even for total `tsum`;
it alone does not put the result in the physical LLL.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

open scoped ComplexConjugate

noncomputable section

/-- Finite-degree physical seed; no infinite plane-LLL boundedness claim. -/
def gaussianPolynomialSeed (k : ℝ) (P : Polynomial ℂ) : ℂ → ℂ :=
  fun z => gaussianFactor k z * P.eval z

/-- One raw image, with inverse chi and unchanged planar scale. -/
def magneticImage (M k : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ)
    (f : ℂ → ℂ) (p : ℤ × ℤ) (z : ℂ) : ℂ :=
  (latticeChi M theta1 theta2 p ^ k)⁻¹ *
    magneticTranslate (k : ℝ) (latticePeriod omega1 omega2 p) f z

/-- Exact series from `eq:periodization`, indexed by lattice coordinates. -/
def magneticPeriodization (M k : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ)
    (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑' p : ℤ × ℤ, magneticImage M k omega1 omega2 theta1 theta2 f p z

/-- Explicit pending convergence domain; this is not a model field or axiom. -/
def HasAbsolutelySummableImages (M k : ℕ) (omega1 omega2 : ℂ)
    (theta1 theta2 : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Summable (fun p : ℤ × ℤ =>
    ‖magneticImage M k omega1 omega2 theta1 theta2 f p z‖)

/-- The paper's planar `e_j`, without any torus Gram renormalization. -/
def planeJet (j : ℕ) : ℂ → ℂ :=
  fun z => gaussianFactor 1 z * z ^ j / (Real.sqrt (j.factorial : ℝ) : ℂ)

/-- `u_j(R) = T_R e_j`, keeping R and the physical coordinate distinct. -/
def translatedPlaneJet (j : ℕ) (R : ℂ) : ℂ → ℂ :=
  magneticTranslate 1 R (planeJet j)

/-- The raw `u_j^T(R) = P_1 u_j(R)` formula, as an actual function of z.
Membership in RawLLL awaits Gaussian-series convergence, not a definition. -/
def rawJetFunction (M : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ)
    (j : ℕ) (R : ℂ) : ℂ → ℂ :=
  magneticPeriodization M 1 omega1 omega2 theta1 theta2 (translatedPlaneJet j R)

theorem gaussianPolynomialSeed_holomorphic (k : ℝ) (P : Polynomial ℂ) :
    IsGaussianHolomorphic k (gaussianPolynomialSeed k P) := by
  exact ⟨fun z => P.eval z, P.differentiable, fun _ => rfl⟩

theorem planeJet_holomorphic (j : ℕ) : IsGaussianHolomorphic 1 (planeJet j) := by
  refine ⟨fun z => z ^ j / (Real.sqrt (j.factorial : ℝ) : ℂ),
    (differentiable_id.pow j).div_const _, ?_⟩
  intro z
  simp only [planeJet, div_eq_mul_inv]
  ring

theorem translatedPlaneJet_holomorphic (j : ℕ) (R : ℂ) :
    IsGaussianHolomorphic 1 (translatedPlaneJet j R) :=
  gaussianHolomorphic_translate 1 R (planeJet j) (planeJet_holomorphic j)

theorem latticeChi_charge_semicharacter (M k : ℕ) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (theta1 theta2 : ℝ) (p q : ℤ × ℤ) :
    latticeChi M theta1 theta2 p ^ k * latticeChi M theta1 theta2 q ^ k =
      magneticCocycle (k : ℝ) (latticePeriod omega1 omega2 p)
        (latticePeriod omega1 omega2 q) * latticeChi M theta1 theta2 (p + q) ^ k := by
  rw [← mul_pow, latticeChi_semicharacter M omega1 omega2 harea,
    mul_pow, magneticCocycle_nat_charge]

/-- Exact image-by-image cocycle cancellation for the physical convention. -/
theorem magneticImage_translate (M k : ℕ) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (theta1 theta2 : ℝ) (f : ℂ → ℂ) (p q : ℤ × ℤ) (z : ℂ) :
    Complex.exp (magneticExponent (k : ℝ) z (latticePeriod omega1 omega2 q)) *
        magneticImage M k omega1 omega2 theta1 theta2 f p
          (z - latticePeriod omega1 omega2 q) =
      latticeChi M theta1 theta2 q ^ k *
        magneticImage M k omega1 omega2 theta1 theta2 f (q + p) z := by
  have hcp : latticeChi M theta1 theta2 p ^ k ≠ 0 :=
    pow_ne_zero k (latticeChi_ne_zero M theta1 theta2 p)
  have hcqp : latticeChi M theta1 theta2 (q + p) ^ k ≠ 0 :=
    pow_ne_zero k (latticeChi_ne_zero M theta1 theta2 (q + p))
  have hs := latticeChi_charge_semicharacter M k omega1 omega2 harea theta1 theta2 q p
  have hphase : (latticeChi M theta1 theta2 p ^ k)⁻¹ *
      magneticCocycle (k : ℝ) (latticePeriod omega1 omega2 q)
        (latticePeriod omega1 omega2 p) =
      latticeChi M theta1 theta2 q ^ k *
        (latticeChi M theta1 theta2 (q + p) ^ k)⁻¹ := by
    calc
      _ = (latticeChi M theta1 theta2 p ^ k)⁻¹ *
          (magneticCocycle (k : ℝ) (latticePeriod omega1 omega2 q)
            (latticePeriod omega1 omega2 p) * latticeChi M theta1 theta2 (q + p) ^ k) *
          (latticeChi M theta1 theta2 (q + p) ^ k)⁻¹ := by
            simp [hcqp, mul_assoc]
      _ = _ := by rw [← hs]; simp [hcp, mul_assoc, mul_left_comm, mul_comm]
  have hcomp := congrFun (magneticTranslate_comp (k : ℝ)
    (latticePeriod omega1 omega2 q) (latticePeriod omega1 omega2 p) f) z
  change Complex.exp (magneticExponent (k : ℝ) z (latticePeriod omega1 omega2 q)) *
      magneticTranslate (k : ℝ) (latticePeriod omega1 omega2 p) f
        (z - latticePeriod omega1 omega2 q) = _ at hcomp
  simp only [magneticImage]
  calc
    _ = (latticeChi M theta1 theta2 p ^ k)⁻¹ *
        (Complex.exp (magneticExponent (k : ℝ) z (latticePeriod omega1 omega2 q)) *
          magneticTranslate (k : ℝ) (latticePeriod omega1 omega2 p) f
            (z - latticePeriod omega1 omega2 q)) := by ring
    _ = _ := by
      rw [hcomp, ← latticePeriod_add, ← mul_assoc, hphase]
      ring

/-- The series has the correct eigencharacter by exact coordinate reindexing.
This is only the boundary substep of T02; analytic LLL membership is pending. -/
theorem magneticPeriodization_boundary (M k : ℕ) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (theta1 theta2 : ℝ) (f : ℂ → ℂ) :
    HasLatticeBoundary M k omega1 omega2 theta1 theta2
      (magneticPeriodization M k omega1 omega2 theta1 theta2 f) := by
  intro q
  funext z
  change Complex.exp (magneticExponent (k : ℝ) z (latticePeriod omega1 omega2 q)) *
      (∑' p : ℤ × ℤ, magneticImage M k omega1 omega2 theta1 theta2 f p
        (z - latticePeriod omega1 omega2 q)) =
    latticeChi M theta1 theta2 q ^ k *
      (∑' p : ℤ × ℤ, magneticImage M k omega1 omega2 theta1 theta2 f p z)
  rw [← tsum_mul_left]
  simp_rw [magneticImage_translate M k omega1 omega2 harea]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addLeft q).tsum_eq (fun p =>
    magneticImage M k omega1 omega2 theta1 theta2 f p z)

#print axioms gaussianPolynomialSeed_holomorphic
#print axioms planeJet_holomorphic
#print axioms translatedPlaneJet_holomorphic
#print axioms latticeChi_charge_semicharacter
#print axioms magneticImage_translate
#print axioms magneticPeriodization_boundary

end

end TorusLean.Geometry
