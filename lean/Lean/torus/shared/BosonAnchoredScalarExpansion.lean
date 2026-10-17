import torus.shared.CoherentJetExpansion
import torus.shared.BosonPairCOMGeneratingCoefficient
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredScalarExpansion
open TorusLean.Geometry TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.CoherentJetExpansion
open TorusLean.Shared.BosonPairCOMCoefficientBound
open TorusLean.Shared.BosonPairCOMGeneratingCoefficient
open scoped BigOperators ComplexConjugate

def primalCoherentWeight (beta : ℂ) (j : ℕ) : ℂ :=
  gaussianFactor 1 beta * beta^j / (Real.sqrt (j.factorial:ℝ):ℂ)

/-- Entire Taylor expansion of the actual back-translated torus section;
the magnetic translation remains in the value, with no dropped phase. -/
theorem primal_coherent_hasSum (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R beta : ℂ) :
    HasSum (fun j => primalCoherentWeight beta j * rawJetCoefficient G theta h j R)
      (magneticTranslate 1 (-R) h.val beta) := by
  have hs := (rawJetCoefficient_taylor_hasSum G theta h R beta).mul_left (gaussianFactor 1 beta)
  have hf := magneticTranslate_stripped_factor (-R) h.val (canonicalRawStripped G theta h)
    (canonicalRawStripped_factor G theta h) beta
  rw [← hf] at hs
  convert hs using 1
  ext j
  simp only [primalCoherentWeight]
  ring

/-- The normalized pair-COM scalar coefficient, before any plane integral.
The sqrt2 cancels the pair creation normalization in the source coefficient. -/
def pairJetCoefficient (G : Geometry) (theta : Twist)
    (f g : RawLLL G theta 1) (R : ℂ) (l : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (l+1), (Real.sqrt (2:ℝ):ℂ) * (pairCOMCoefficientReal l i : ℂ) *
    rawJetCoefficient G theta f i R * rawJetCoefficient G theta g (l-i) R

theorem pair_generating_factor (l i : ℕ) (hi : i ≤ l) :
    ((Real.sqrt (2:ℝ):ℂ)^l / (Real.sqrt (l.factorial:ℝ):ℂ)) *
      (Real.sqrt (2:ℝ):ℂ) * (pairCOMCoefficientReal l i : ℂ) =
      1 / ((Real.sqrt (i.factorial:ℝ):ℂ) * (Real.sqrt ((l-i).factorial:ℝ):ℂ)) := by
  have h : ((Real.sqrt (2:ℝ):ℂ)^l / (Real.sqrt (l.factorial:ℝ):ℂ)) *
      (pairCOMCoefficientReal l i : ℂ) =
      (1 / (Real.sqrt (2:ℝ):ℂ)) /
        ((Real.sqrt (i.factorial:ℝ):ℂ) * (Real.sqrt ((l-i).factorial:ℝ):ℂ)) := by
    exact_mod_cast pairCOMCoefficientReal_generating l i hi
  calc
    _ = (Real.sqrt (2:ℝ):ℂ) *
      (((Real.sqrt (2:ℝ):ℂ)^l / (Real.sqrt (l.factorial:ℝ):ℂ)) *
        (pairCOMCoefficientReal l i : ℂ)) := by ring
    _ = _ := by
      rw [h]
      have h2 : (Real.sqrt (2:ℝ):ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt (2:ℝ) ≠ 0 by positivity)
      have hi0 : (Real.sqrt (i.factorial:ℝ):ℂ) ≠ 0 := by
        exact_mod_cast (show Real.sqrt (i.factorial:ℝ) ≠ 0 by positivity)
      have hj0 : (Real.sqrt ((l-i).factorial:ℝ):ℂ) ≠ 0 := by
        exact_mod_cast (show Real.sqrt ((l-i).factorial:ℝ) ≠ 0 by positivity)
      field_simp [h2,hi0,hj0]


def pairCoherentWeight (beta : ℂ) (l : ℕ) : ℂ :=
  gaussianFactor 1 beta ^ 2 * beta^l * (Real.sqrt (2:ℝ):ℂ)^l /
    (Real.sqrt (l.factorial:ℝ):ℂ)

/-- Cauchy's product is applied only to the two absolutely convergent actual
Taylor expansions. The normalized pair coefficients are identified termwise. -/
theorem pair_coherent_hasSum (G : Geometry) (theta : Twist)
    (f g : RawLLL G theta 1) (R beta : ℂ) :
    HasSum (fun l => pairCoherentWeight beta l * pairJetCoefficient G theta f g R l)
      (magneticTranslate 1 (-R) f.val beta * magneticTranslate 1 (-R) g.val beta) := by
  have hf := primal_coherent_hasSum G theta f R beta
  have hg := primal_coherent_hasSum G theta g R beta
  have hs := hasSum_sum_range_mul_of_summable_norm hf.summable.norm hg.summable.norm
  rw [hf.tsum_eq,hg.tsum_eq] at hs
  apply hs.congr_fun
  intro l
  simp only [pairJetCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i ≤ l := by have := Finset.mem_range.mp hi; omega
  have he : i+(l-i)=l := by omega
  symm
  calc
    _ = gaussianFactor 1 beta ^ 2 * (beta^i * beta^(l-i)) *
      (1 / ((Real.sqrt (i.factorial:ℝ):ℂ) * (Real.sqrt ((l-i).factorial:ℝ):ℂ))) *
      rawJetCoefficient G theta f i R * rawJetCoefficient G theta g (l-i) R := by
        simp only [primalCoherentWeight,div_eq_mul_inv,mul_inv_rev]
        ring
    _ = _ := by
      rw [←pow_add,he,←pair_generating_factor l i hil]
      unfold pairCoherentWeight
      ring

end TorusLean.Shared.BosonAnchoredScalarExpansion
