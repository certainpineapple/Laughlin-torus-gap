import torus.shared.ParameterLadderScaling

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterLadderScaling
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterLadderIntegration

theorem scaledCOMLevels_isLadder (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hb : ∀ n, HasDualBoundary G theta k (f n))
    (hR : ∀ n R, (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (f n) R = f (n+1) R)
    (hL0 : parameterLower k (f 0) = 0)
    (hL : ∀ n R, (Real.sqrt (k:ℝ):ℂ)*parameterLower k (f (n+1)) R =
      (k:ℂ)*((n+1:ℕ):ℂ)*f n R) :
    IsLadderFamily G theta k (scaledCOMLevels k f) := by
  have hh (H : ℕ) := scaledCOMLevels_isFiniteLadder G theta k H f
    (fun n _ => hf n) (fun n _ => hb n) (fun n _ => hR n) hL0 (fun n _ => hL n)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro n; exact (hh n).smooth n (by omega)
  · intro n; exact (hh n).boundary n (by omega)
  · intro n; exact (hh (n+1)).raise_eq n (by omega)
  · exact (hh 0).lower_zero
  · intro n; exact (hh (n+1)).lower_succ n (by omega)

end TorusLean.Shared.ParameterLadderScaling
