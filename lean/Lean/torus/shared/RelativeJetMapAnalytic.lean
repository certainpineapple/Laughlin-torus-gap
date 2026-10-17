import torus.shared.NormalJetBridge
import torus.shared.CellHilbert
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
Analytic and magnetic geometry for the original relative jet. All functions
are actual universal-cover sections. No relative frame estimate, image
characterization or COM equivalence is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.NormalJetBridge
open scoped TensorProduct ComplexConjugate

/-- The full algebraic tensor has a jointly entire Gaussian factor. -/
theorem rawPairFunction_joint_factor (G : Geometry) (theta : Twist) (a b : ℕ)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) :
    ∃ F : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
      ∀ z, rawPairFunction G theta a b ψ z =
        (gaussianFactor a z.1 * gaussianFactor b z.2) * F z := by
  induction ψ using TensorProduct.induction_on with
  | zero =>
    exact ⟨0, analyticOnNhd_const, by intro z; simp⟩
  | tmul f g =>
    obtain ⟨F, hF, hf⟩ := f.property.1
    obtain ⟨H, hH, hg⟩ := g.property.1
    refine ⟨fun z => F z.1 * H z.2, ?_, ?_⟩
    · intro z _
      exact ((hF.analyticAt z.1).comp analyticAt_fst).mul
        ((hH.analyticAt z.2).comp analyticAt_snd)
    · intro z
      rw [rawPairFunction_tmul_apply, hf, hg]
      ring
  | add ψ φ hψ hφ =>
    obtain ⟨F, hF, hf⟩ := hψ
    obtain ⟨H, hH, hg⟩ := hφ
    refine ⟨F + H, hF.add hH, ?_⟩
    intro z
    simp only [map_add, Pi.add_apply, hf, hg]
    ring

/-- The line in the relative direction before its COM basepoint is added. -/
def normalLine (a b : ℝ) : ℂ →L[ℂ] ℂ × ℂ :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight
    (((b / (a+b) : ℝ) : ℂ), -((a / (a+b) : ℝ) : ℂ))

@[simp] theorem normalLine_apply (a b : ℝ) (r : ℂ) :
    normalLine a b r =
      (((b / (a+b) : ℝ) : ℂ) * r, -((a / (a+b) : ℝ) : ℂ) * r) := by
  simp [normalLine, mul_comm]

/-- The ordinary relative derivative is the actual joint derivative applied
in the weighted Jacobi direction. This is an all-point identity. -/
theorem normal_iteratedDeriv_eq (a b : ℝ) (d : ℕ) (F : ℂ × ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (C : ℂ) :
    iteratedDeriv d (fun r : ℂ => F (jacobiFirst a b C r, jacobiSecond a b C r)) 0 =
      iteratedFDeriv ℂ d F (C,C)
        (fun _ : Fin d => (((b/(a+b) : ℝ) : ℂ), -((a/(a+b) : ℝ) : ℂ))) := by
  let H : ℂ × ℂ → ℂ := fun z => F ((C,C) + z)
  have hH : ContDiff ℂ d H := hF.contDiff.comp (contDiff_const.add contDiff_id)
  have heq : (fun r : ℂ => F (jacobiFirst a b C r, jacobiSecond a b C r)) =
      H ∘ normalLine a b := by
    funext r
    simp [H, jacobiFirst, jacobiSecond, sub_eq_add_neg]
  rw [heq, iteratedDeriv_eq_iteratedFDeriv,
    (normalLine a b).iteratedFDeriv_comp_right hH 0 le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, normalLine_apply,
    mul_zero, mul_one, Prod.mk_zero_zero, H,
    iteratedFDeriv_comp_add_left, add_zero]

/-- Arbitrary relative derivatives remain entire in the COM coordinate. -/
theorem normal_iteratedDeriv_analytic (a b : ℝ) (d : ℕ) (F : ℂ × ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) :
    AnalyticOnNhd ℂ (fun C => iteratedDeriv d
      (fun r : ℂ => F (jacobiFirst a b C r, jacobiSecond a b C r)) 0) Set.univ := by
  have hD := hF.iteratedFDeriv d
  let v : Fin d → ℂ × ℂ :=
    fun _ => (((b/(a+b) : ℝ) : ℂ), -((a/(a+b) : ℝ) : ℂ))
  intro C _
  simp_rw [normal_iteratedDeriv_eq a b d F hF]
  have hdiag : AnalyticAt ℂ (fun z : ℂ => (z,z)) C := by fun_prop
  have hcomp := (hD (C,C) (Set.mem_univ _)).comp (f := fun z : ℂ => (z,z)) hdiag
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin d => ℂ × ℂ) ℂ v).analyticAt _).comp hcomp

/-- Membership's differential half is proved from the original Gaussian
cancellation and joint entire factor, for arbitrary nonzero total charge. -/
theorem localNormalJet_gaussianHolomorphic (a b : ℝ) (hab : a+b ≠ 0)
    (d : ℕ) (Ψ F : ℂ × ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (hΨ : ∀ z, Ψ z = (gaussianFactor a z.1 * gaussianFactor b z.2) * F z) :
    IsGaussianHolomorphic (a+b) (localNormalJet a b d Ψ) := by
  refine ⟨fun C => (jetScale a b d)⁻¹ * iteratedDeriv d
    (fun r : ℂ => F (jacobiFirst a b C r, jacobiSecond a b C r)) 0, ?_, ?_⟩
  · intro C
    exact ((normal_iteratedDeriv_analytic a b d F hF) C (Set.mem_univ _)).differentiableAt.const_mul _
  · intro C
    rw [localNormalJet_gaussian_factor a b hab d Ψ F 1 (by simpa using hΨ)]
    ring

end TorusLean.Shared.RelativeJetMap
