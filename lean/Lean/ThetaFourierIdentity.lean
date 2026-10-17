import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false

namespace TorusLean.Geometry.ThetaFourier

open Filter Set
open scoped Topology

/-- Agreement of two entire functions on the real axis determines their
values on all of `ℂ`. The identity principle applies at zero using the
nonzero real sequence `(1 / 2) ^ n`, which tends to zero. -/
theorem entire_eq_of_eq_on_real (F G : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hreal : ∀ t : ℝ, F (t : ℂ) = G (t : ℂ)) : F = G := by
  have hseq : Tendsto (fun n : ℕ => (((1 / 2 : ℝ) ^ n : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) := by
    have hseqR := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using hseqR.ofReal
  have hclosure : (0 : ℂ) ∈ closure ({z | F z = G z} \ {(0 : ℂ)}) := by
    refine mem_closure_of_tendsto hseq (Eventually.of_forall fun n => ?_)
    refine ⟨hreal ((1 / 2 : ℝ) ^ n), ?_⟩
    simp only [mem_singleton_iff, Complex.ofReal_eq_zero]
    exact pow_ne_zero n (by norm_num)
  have hFA : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  have hGA : AnalyticOnNhd ℂ G univ := fun z _ => hG.analyticAt z
  have hagree := hFA.eqOn_of_preconnected_of_mem_closure hGA
    isPreconnected_univ (mem_univ (0 : ℂ)) hclosure
  exact funext fun z => hagree (mem_univ z)

end TorusLean.Geometry.ThetaFourier
