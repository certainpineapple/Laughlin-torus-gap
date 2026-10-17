import torus.shared.ThermalCoherentJacobiInsertion
import Mathlib.Data.Nat.Choose.Sum

/-! Explicit finite binomial coefficients of the actual normalized pair-COM
source. Ordered particle contributions, including equal labels, are retained.
The square-root factorial convention is the original canonical oscillator one. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open scoped BigOperators

/-- Iterating the genuine pair COM derivation yields the exact finite
binomial polynomial, not an independently postulated pair source. -/
theorem pairRaised_binomial (p : ℕ) : pairRaised p =
    (Real.sqrt (2:ℝ) : ℂ)⁻¹ • ∑ i ∈ Finset.range (p+1),
      p.choose i • (spectatorScaled i * spectatorScaled (p-i)) := by
  induction p with
  | zero => simp [pairRaised_zero, pairVacuum, spectatorScaled, factorialRootNat, pow_two]
  | succ p ih =>
    rw [pairRaised_succ, ih, map_smul, map_sum]
    simp only [map_nsmul, canonicalCOMRaiseNat_mul, spectatorScaled_raise, nsmul_add,
      Finset.sum_add_distrib]
    rw [show p+1+1=p+2 by omega,
      Finset.sum_choose_succ_nsmul (fun i j => spectatorScaled i * spectatorScaled j) p]
    congr 1
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show p+1-i=(p-i)+1 by have := Finset.mem_range.mp hi; omega]

/-- Canonical pair-COM level with its exact factorial-root coefficients.
This is the binomial pair polynomial equivalent to the usual sqrt-choose
notation, with no normalization of its image under torus periodization. -/
theorem pairCOMSeed_binomial (p : ℕ) : pairCOMSeed p =
    ((Real.sqrt ((2:ℝ)^p * (p.factorial:ℝ)) : ℂ)⁻¹ * (Real.sqrt (2:ℝ) : ℂ)⁻¹) •
      ∑ i ∈ Finset.range (p+1), p.choose i •
        ((factorialRootNat i * factorialRootNat (p-i)) •
          ((MvPolynomial.X i : Core ℕ ℂ) * MvPolynomial.X (p-i))) := by
  rw [pairCOMSeed, pairRaised_binomial, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [spectatorScaled, smul_mul_smul_comm]

end TorusLean.Shared.ThermalCoherentJacobiInsertion
