import torus.shared.FermionM1NearProjectionSum

/-! Quantitative near projection for the actual m=1 relative derivative.
The right side is its own physical energy, never an arbitrary auxiliary form.
Transport to the many-body CAR Hamiltonian is a separate physical identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionM1NearProjection
open TorusLean.Geometry TorusLean.Fermion.LatticePacking
open Filter Topology
open scoped TensorProduct

/-- Full charge-two COM quadratic error of the actual QQ-adjoint. -/
theorem m1Q_output_form_error (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (f : LLL G theta 2) :
    |(inner ℂ f (((m1Q G theta).comp (m1Q G theta).adjoint -
      ContinuousLinearMap.id ℂ (LLL G theta 2)) f)).re| ≤ m1GramError L * ‖f‖^2 := by
  let E := (m1Q G theta).comp (m1Q G theta).adjoint -
    ContinuousLinearMap.id ℂ (LLL G theta 2)
  have hb : ‖E f‖ ≤ m1GramError L * ‖f‖ :=
    (E.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (m1Q_defect_bound G theta L hL1 hL) (norm_nonneg _))
  calc
    _ ≤ ‖inner ℂ f (E f)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖f‖ * ‖E f‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖ * (m1GramError L * ‖f‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

/-- The inherited full-tensor physical pair operator for the genuine J1. -/
def m1PairOperator (G : Geometry) (theta : Twist) :
    (LLL G theta 1 ⊗[ℂ] LLL G theta 1) →L[ℂ]
      (LLL G theta 1 ⊗[ℂ] LLL G theta 1) :=
  (m1Q G theta).adjoint.comp (m1Q G theta)

theorem m1PairOperator_form (G : Geometry) (theta : Twist)
    (ψ : LLL G theta 1 ⊗[ℂ] LLL G theta 1) :
    (inner ℂ ψ (m1PairOperator G theta ψ)).re = ‖m1Q G theta ψ‖^2 := by
  rw [m1PairOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (m1Q G theta ψ)).symm

/-- Actual same-pair-energy payment: h²-h is controlled by h itself. -/
theorem m1PairOperator_same_energy_error (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (ψ : LLL G theta 1 ⊗[ℂ] LLL G theta 1) :
    |(inner ℂ ψ (((m1PairOperator G theta).comp (m1PairOperator G theta) -
      m1PairOperator G theta) ψ)).re| ≤
        m1GramError L * (inner ℂ ψ (m1PairOperator G theta ψ)).re := by
  have he : inner ℂ ψ (((m1PairOperator G theta).comp (m1PairOperator G theta) -
      m1PairOperator G theta) ψ) =
      inner ℂ (m1Q G theta ψ) (((m1Q G theta).comp (m1Q G theta).adjoint -
        ContinuousLinearMap.id ℂ (LLL G theta 2)) (m1Q G theta ψ)) := by
    simp only [m1PairOperator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, inner_sub_right,
      ContinuousLinearMap.adjoint_inner_right]
  rw [he, m1PairOperator_form]
  exact m1Q_output_form_error G theta L hL1 hL (m1Q G theta ψ)

/-- Full COM adjoint norms have the same uniform error without mode-count loss. -/
theorem m1Q_adjoint_norm_error (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (f : LLL G theta 2) :
    |‖(m1Q G theta).adjoint f‖^2 - ‖f‖^2| ≤ m1GramError L * ‖f‖^2 := by
  have h := m1Q_output_form_error G theta L hL1 hL f
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, Complex.sub_re] at h
  rw [← ContinuousLinearMap.adjoint_inner_left] at h
  have hn₁ : ‖(m1Q G theta).adjoint f‖^2 =
      (inner ℂ ((m1Q G theta).adjoint f) ((m1Q G theta).adjoint f)).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  have hn₂ : ‖f‖^2 = (inner ℂ f f).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  rw [← hn₁, ← hn₂] at h
  exact h

/-- One tolerance threshold for the actual map on every original geometry. -/
theorem m1Q_exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ‖(m1Q G theta).comp (m1Q G theta).adjoint -
        ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤ ε := by
  obtain ⟨L, hL1, hL⟩ := m1GramError_exists_threshold ε hε
  refine ⟨L, hL1, fun G theta hG => ?_⟩
  exact (m1Q_defect_bound G theta (systole G) (hL1.trans hG) le_rfl).trans
    (hL (systole G) hG)

#print axioms m1Q_output_form_error
#print axioms m1PairOperator_form
#print axioms m1PairOperator_same_energy_error
#print axioms m1Q_adjoint_norm_error
#print axioms m1Q_exists_threshold
end TorusLean.Shared.FermionM1NearProjection
