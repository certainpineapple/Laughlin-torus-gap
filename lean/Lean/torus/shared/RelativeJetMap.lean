import torus.shared.RelativeJetMapBoundary

/-!
# The actual bounded full-tensor relative jet

The domain is the complete physical charge-a by charge-b Hilbert tensor,
with the cell-induced tensor norm. The codomain is the whole pre-existing
charge-(a+b) LLL, not an image-defined space. Its value is the original
localNormalJet at every point. Analyticity, all-period magnetic boundary,
linearity and boundedness are proved; no Gram or frame estimate is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.NormalJetBridge
open scoped TensorProduct ComplexConjugate

/-- The Gaussian-corrected slice in the original derivative definition. -/
def correctedPairSlice (G : Geometry) (theta : Twist) (a b : ℕ)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) (C r : ℂ) : ℂ :=
  Complex.exp ((relativeCharge a b : ℂ) * (r * conj r) / 2) *
    rawPairFunction G theta a b ψ (jacobiFirst a b C r, jacobiSecond a b C r)

/-- Required regularity for derivative additivity is derived, not assumed. -/
theorem correctedPairSlice_analytic (G : Geometry) (theta : Twist) (a b : ℕ)
    (hab : (a:ℝ)+(b:ℝ) ≠ 0)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) (C : ℂ) :
    AnalyticOnNhd ℂ (correctedPairSlice G theta a b ψ C) Set.univ := by
  obtain ⟨F, hF, hψ⟩ := rawPairFunction_joint_factor G theta a b ψ
  have heq : correctedPairSlice G theta a b ψ C = fun r =>
      gaussianFactor ((a:ℝ)+(b:ℝ)) C *
        F (jacobiFirst a b C r, jacobiSecond a b C r) := by
    funext r
    simp only [correctedPairSlice, hψ]
    rw [← mul_assoc, jacobi_covariant_gaussian_cancel (a:ℝ) (b:ℝ) hab]
  rw [heq]
  intro r _
  have hcoord : AnalyticAt ℂ
      (fun r : ℂ => (jacobiFirst a b C r, jacobiSecond a b C r)) r := by
    unfold jacobiFirst jacobiSecond
    fun_prop
  exact analyticAt_const.mul ((hF _ (Set.mem_univ _)).comp hcoord)

/-- Every tensor's original local jet lands in the whole original section
carrier; this theorem supplies both defining predicates of that carrier. -/
theorem rawPairFunction_normalJet_mem (G : Geometry) (theta : Twist)
    (a b : ℕ) (hab : (a:ℝ)+(b:ℝ) ≠ 0) (d : ℕ)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) :
    localNormalJet a b d (rawPairFunction G theta a b ψ) ∈
      rawLLLSubmodule G.M (a+b) G.omega1 G.omega2 theta.theta1 theta.theta2 := by
  obtain ⟨F, hF, hψ⟩ := rawPairFunction_joint_factor G theta a b ψ
  constructor
  · simpa only [Nat.cast_add] using
      localNormalJet_gaussianHolomorphic a b hab d _ F hF hψ
  · exact rawPairFunction_normalJet_boundary G theta a b hab d ψ

/-- Linearity of the actual local derivative on arbitrary full tensors. -/
theorem rawPairFunction_normalJet_add (G : Geometry) (theta : Twist)
    (a b : ℕ) (hab : (a:ℝ)+(b:ℝ) ≠ 0) (d : ℕ)
    (ψ φ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) :
    localNormalJet a b d (rawPairFunction G theta a b (ψ+φ)) =
      localNormalJet a b d (rawPairFunction G theta a b ψ) +
        localNormalJet a b d (rawPairFunction G theta a b φ) := by
  funext C
  have heq : correctedPairSlice G theta a b (ψ+φ) C =
      correctedPairSlice G theta a b ψ C + correctedPairSlice G theta a b φ C := by
    funext r
    simp only [correctedPairSlice, map_add, Pi.add_apply, mul_add]
  change (jetScale a b d)⁻¹ * iteratedDeriv d (correctedPairSlice G theta a b (ψ+φ) C) 0 =
    (jetScale a b d)⁻¹ * iteratedDeriv d (correctedPairSlice G theta a b ψ C) 0 +
      (jetScale a b d)⁻¹ * iteratedDeriv d (correctedPairSlice G theta a b φ C) 0
  rw [heq, iteratedDeriv_add
    (correctedPairSlice_analytic G theta a b hab ψ C).contDiff.contDiffAt
    (correctedPairSlice_analytic G theta a b hab φ C).contDiff.contDiffAt, mul_add]

theorem rawPairFunction_normalJet_smul (G : Geometry) (theta : Twist)
    (a b d : ℕ) (c : ℂ)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) :
    localNormalJet a b d (rawPairFunction G theta a b (c • ψ)) =
      c • localNormalJet a b d (rawPairFunction G theta a b ψ) := by
  funext C
  have heq : correctedPairSlice G theta a b (c • ψ) C =
      fun r => c * correctedPairSlice G theta a b ψ C r := by
    funext r
    simp only [correctedPairSlice, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  change (jetScale a b d)⁻¹ * iteratedDeriv d (correctedPairSlice G theta a b (c • ψ) C) 0 =
    c * ((jetScale a b d)⁻¹ * iteratedDeriv d (correctedPairSlice G theta a b ψ C) 0)
  rw [heq, iteratedDeriv_const_mul_field]
  ring

/-- Full physical domain and full physical codomain. The function is the
original formula; its carrier membership is the theorem just proved. -/
def relativeJetLinearMap (G : Geometry) (theta : Twist) (a b d : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)] :
    (LLL G theta a ⊗[ℂ] LLL G theta b) →ₗ[ℂ] LLL G theta (a+b) where
  toFun ψ := ⟨localNormalJet a b d (rawPairFunction G theta a b ψ),
    rawPairFunction_normalJet_mem G theta a b
      (by exact_mod_cast (Nat.add_pos_left (NeZero.pos a) b).ne') d ψ⟩
  map_add' ψ φ := Subtype.ext (rawPairFunction_normalJet_add G theta a b
    (by exact_mod_cast (Nat.add_pos_left (NeZero.pos a) b).ne') d ψ φ)
  map_smul' c ψ := Subtype.ext (rawPairFunction_normalJet_smul G theta a b d c ψ)

/-- Boundedness uses only the already derived finite dimension of the actual
cell Hilbert tensor. No new frame completeness or quantitative bound enters. -/
def relativeJet (G : Geometry) (theta : Twist) (a b d : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)] :
    (LLL G theta a ⊗[ℂ] LLL G theta b) →L[ℂ] LLL G theta (a+b) :=
  (relativeJetLinearMap G theta a b d).toContinuousLinearMap

/-- Pointwise identification for every full tensor, not only pure tensors. -/
theorem relativeJet_apply (G : Geometry) (theta : Twist) (a b d : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)]
    (ψ : LLL G theta a ⊗[ℂ] LLL G theta b) (C : ℂ) :
    (relativeJet G theta a b d ψ).val C =
      localNormalJet a b d (rawPairFunction G theta a b ψ) C := rfl

/-- Original physical cell norm, with no coordinate-space replacement. -/
theorem relativeJet_cell_norm_sq (G : Geometry) (theta : Twist) (a b d : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)]
    (ψ : LLL G theta a ⊗[ℂ] LLL G theta b) :
    ‖relativeJet G theta a b d ψ‖^2 =
      ∫ C, ‖localNormalJet a b d (rawPairFunction G theta a b ψ) C‖^2
        ∂cellMeasure G (a+b) :=
  lll_norm_sq_eq_cellIntegral G theta (a+b) _

theorem relativeJet_bound (G : Geometry) (theta : Twist) (a b d : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)]
    (ψ : LLL G theta a ⊗[ℂ] LLL G theta b) :
    ‖relativeJet G theta a b d ψ‖ ≤ ‖relativeJet G theta a b d‖ * ‖ψ‖ :=
  (relativeJet G theta a b d).le_opNorm ψ

/-- Degree zero is precisely the already existing unrescaled product map. -/
theorem relativeJet_zero_eq_product (G : Geometry) (theta : Twist) (a b : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)]
    (ψ : LLL G theta a ⊗[ℂ] LLL G theta b) :
    (relativeJet G theta a b 0 ψ).val = (rawProductQ G theta a b ψ).val := by
  funext C
  rw [relativeJet_apply, rawProductQ_apply_eq_diagonal]
  simp [localNormalJet, jacobiFirst, jacobiSecond]

end TorusLean.Shared.RelativeJetMap
