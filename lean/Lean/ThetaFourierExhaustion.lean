import ThetaFourier
import ThetaFourierContour
import ThetaFourierIdentity

set_option autoImplicit false

/-!
Exhaustion of actual entire theta sections by the constructed Jacobi-theta
functions. The coefficients are extracted by a real-cycle integral, their
recurrence is obtained by translating that integral, and Fourier uniqueness
on the circle followed by the complex identity principle recovers the section.
No coefficient-summability or reconstruction hypothesis is assumed.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaFourier

open Complex Real ContinuousMap
open ThetaAnalytic ThetaFactorization

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- An arbitrary entire section's actual integral coefficients belong to the
previously classified recurrence space. -/
def extractedRecurrence (d : ℕ) (tau sigma psi : ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z)
    (ht : ∀ z : ℂ, F (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z) :
    thetaRecurrenceSpace d (π * I * tau) (-I * psi) sigma := by
  refine ⟨fourierExtract sigma F, ?_⟩
  intro n
  simpa only [sub_eq_add_neg, neg_mul] using
    fourierExtract_recurrence sigma psi tau d F hF h1 ht n

theorem untwist_real_periodic (sigma : ℂ) (F : ℂ → ℂ)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z) :
    Function.Periodic (fun t : ℝ => untwist sigma F (t : ℂ)) 1 := by
  intro t
  simpa [fourierIntegrand, untwist, Complex.ofReal_add] using
    fourierIntegrand_periodic sigma F h1 0 (t : ℂ)

/-- The full untwisted real restriction, including the section itself, descends
to a continuous function on the circle. -/
def untwistedCircle (sigma : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun := (untwist_real_periodic sigma F h1).lift
  continuous_toFun := by
    have hc : Continuous (fun t : ℝ => untwist sigma F (t : ℂ)) :=
      ((Complex.continuous_ofReal.const_mul _).cexp).mul
        (hF.continuous.comp Complex.continuous_ofReal)
    exact hc.quotient_liftOn' _

theorem untwistedCircle_coe (sigma : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z) (t : ℝ) :
    untwistedCircle sigma F hF h1 (t : AddCircle (1 : ℝ)) =
      untwist sigma F (t : ℂ) := rfl

theorem extractedCoefficients_summable (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z)
    (ht : ∀ z : ℂ, F (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z) :
    Summable (fourierExtract sigma F) := by
  let c := extractedRecurrence d tau sigma psi F hF h1 ht
  have he (n : ℤ) : fourierExtract sigma F n =
      constructedCoefficients d tau sigma psi (recurrenceResidues d tau sigma psi c) n :=
    recurrenceCoefficients_eq d tau sigma psi c n
  exact (constructedCoefficients_summable d tau sigma psi hτ
    (recurrenceResidues d tau sigma psi c)).congr fun n => (he n).symm

/-- Every entire function satisfying the exact two boundary laws is one of the
already constructed normally convergent theta combinations. -/
theorem entireSection_exhaustion (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z)
    (ht : ∀ z : ℂ, F (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z) :
    ∃ v : ZMod d → ℂ, F = realizedSection d tau sigma psi v := by
  let c := extractedRecurrence d tau sigma psi F hF h1 ht
  let v := recurrenceResidues d tau sigma psi c
  let G := untwistedCircle sigma F hF h1
  have hc (n : ℤ) : fourierExtract sigma F n =
      constructedCoefficients d tau sigma psi v n :=
    recurrenceCoefficients_eq d tau sigma psi c n
  have hG : ∀ t : ℝ, untwist sigma F (t : ℂ) = G (t : AddCircle (1 : ℝ)) :=
    fun _ => rfl
  have hcoeff (n : ℤ) : fourierCoeff G n =
      fourierCoeff (fourierSeries (constructedCoefficients d tau sigma psi v)) n := by
    rw [← fourierExtract_eq_circleCoeff sigma F G hG n, hc n,
      coefficient_fourierSeries _ (constructedCoefficients_summable d tau sigma psi hτ v)]
  have hcircle := continuous_eq_of_fourierCoeff_eq G
    (fourierSeries (constructedCoefficients d tau sigma psi v)) hcoeff
  have hreal (t : ℝ) : F (t : ℂ) = realizedSection d tau sigma psi v (t : ℂ) := by
    have he : untwist sigma F (t : ℂ) =
        untwist sigma (realizedSection d tau sigma psi v) (t : ℂ) := by
      rw [hG t, hcircle, realizedSection_real_axis d tau sigma psi hτ v t]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) he
  exact ⟨v, entire_eq_of_eq_on_real F (realizedSection d tau sigma psi v) hF
    (realizedSection_differentiable d tau sigma psi hτ v) hreal⟩

theorem entireSection_unique_representation (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z)
    (ht : ∀ z : ℂ, F (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z) :
    ∃! v : ZMod d → ℂ, F = realizedSection d tau sigma psi v := by
  obtain ⟨v, hv⟩ := entireSection_exhaustion d tau sigma psi hτ F hF h1 ht
  refine ⟨v, hv, fun w hw => ?_⟩
  exact realizedSection_injective d tau sigma psi hτ (hw.symm.trans hv)

/-- The extracted integral coefficients reconstruct an arbitrary entire
section at every complex point as an unconditional, absolutely convergent sum. -/
theorem extractedFourier_hasSum (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z)
    (ht : ∀ z : ℂ, F (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z) (z : ℂ) :
    HasSum (fun n : ℤ => fourierExtract sigma F n *
      exp (2 * π * I * ((n : ℂ) + sigma) * z)) (F z) := by
  obtain ⟨v, hv⟩ := entireSection_exhaustion d tau sigma psi hτ F hF h1 ht
  rw [hv]
  have h := weightedFourierTerm_hasSum d tau sigma psi hτ v z
  change HasSum (fun n : ℤ => weightedFourierTerm d tau sigma psi v z n) _ at h
  simpa only [fourierExtract_realizedSection d tau sigma psi hτ v,
    constructedCoefficients, weightedFourierTerm] using h

/-- The Fourier expansion extracted from an arbitrary entire section converges
normally on every compact subset of the complex plane. -/
theorem extractedFourier_normal_convergence (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (h1 : ∀ z : ℂ, F (z + 1) = exp (2 * π * I * sigma) * F z)
    (ht : ∀ z : ℂ, F (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ b : ℤ → ℝ, Summable b ∧ ∀ z ∈ K, ∀ n : ℤ,
      ‖fourierExtract sigma F n * exp (2 * π * I * ((n : ℂ) + sigma) * z)‖ ≤ b n := by
  obtain ⟨v, hv⟩ := entireSection_exhaustion d tau sigma psi hτ F hF h1 ht
  rw [hv]
  simpa only [fourierExtract_realizedSection d tau sigma psi hτ v,
    constructedCoefficients, weightedFourierTerm] using
    weightedFourierTerm_normal_convergence d tau sigma psi hτ v K hK

end TorusLean.Geometry.ThetaFourier
