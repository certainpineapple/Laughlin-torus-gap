import torus.shared.CellHilbert
import Sym2Evaluation
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
The concrete cell contact diagonal and pair operator on the physical Sym² LLL.
Q is the actual diagonal evaluation into the full charge-two physical LLL;
the inner product is the fixed (2/pi)-weighted cell integral. Its adjoint and
positive pair operator are obtained from this proved Hilbert structure.

Riesz evaluation kernels are constructed on these physical spaces. Equality
with the paper's periodized oscillator kernels and quantitative geometric
bounds remain separate obligations. No many-body lift or Hamiltonian is
defined here, and no kernel dimension or gap is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared

open MeasureTheory
open TorusLean.Boson.Sym2Evaluation
open scoped TensorProduct ComplexConjugate

/-- A type synonym keeps the actual inherited tensor norm as the unique
physical topology used by adjoints, rather than the raw function topology. -/
def PhysicalSym2 (G : Geometry) (theta : Twist) :=
  TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)

instance physicalSym2AddCommGroup (G : Geometry) (theta : Twist) :
    AddCommGroup (PhysicalSym2 G theta) :=
  inferInstanceAs (AddCommGroup (TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)))

instance physicalSym2Module (G : Geometry) (theta : Twist) :
    Module ℂ (PhysicalSym2 G theta) :=
  inferInstanceAs (Module ℂ (TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)))

instance physicalSym2NormedAddCommGroup (G : Geometry) (theta : Twist) :
    NormedAddCommGroup (PhysicalSym2 G theta) :=
  inferInstanceAs (NormedAddCommGroup
    (TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)))

instance physicalSym2NormedSpace (G : Geometry) (theta : Twist) :
    NormedSpace ℂ (PhysicalSym2 G theta) :=
  inferInstanceAs (NormedSpace ℂ (TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)))

instance physicalSym2InnerProductSpace (G : Geometry) (theta : Twist) :
    InnerProductSpace ℂ (PhysicalSym2 G theta) :=
  inferInstanceAs (InnerProductSpace ℂ
    (TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)))

instance physicalSym2FiniteDimensional (G : Geometry) (theta : Twist) :
    FiniteDimensional ℂ (PhysicalSym2 G theta) :=
  inferInstanceAs (FiniteDimensional ℂ
    (TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)))

instance physicalSym2Complete (G : Geometry) (theta : Twist) :
    CompleteSpace (PhysicalSym2 G theta) :=
  FiniteDimensional.complete ℂ (PhysicalSym2 G theta)

/-- The unrescaled physical diagonal, restricted to the actual symmetric
square. Boundedness follows from the derived finite physical dimension. -/
def contactQ (G : Geometry) (theta : Twist) :
    PhysicalSym2 G theta →L[ℂ] LLL G theta 2 :=
  let Qlin : PhysicalSym2 G theta →ₗ[ℂ] LLL G theta 2 :=
    (rawContactQ G theta).comp (TorusLean.Boson.Sym2Evaluation.Sym2 (LLL G theta 1)).subtype
  Qlin.toContinuousLinearMap

theorem contactQ_apply (G : Geometry) (theta : Twist)
    (ψ : PhysicalSym2 G theta) (R : ℂ) :
    (contactQ G theta ψ).val R = rawPairFunction G theta 1 1 ψ.val (R, R) :=
  rawContactQ_apply_eq_diagonal G theta ψ.val R

/-- Actual Riesz representative of physical charge-k point evaluation. -/
def evaluationKernel (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (R : ℂ) : LLL G theta k :=
  (InnerProductSpace.toDual ℂ (LLL G theta k)).symm (lllEvaluation G theta k R)

theorem evaluationKernel_reproduces (G : Geometry) (theta : Twist) (k : ℕ)
    [NeZero k] (R : ℂ) (f : LLL G theta k) :
    inner ℂ (evaluationKernel G theta k R) f = f.val R :=
  InnerProductSpace.toDual_symm_apply

theorem evaluationKernel_norm (G : Geometry) (theta : Twist) (k : ℕ)
    [NeZero k] (R : ℂ) :
    ‖evaluationKernel G theta k R‖ = ‖lllEvaluation G theta k R‖ :=
  (InnerProductSpace.toDual ℂ (LLL G theta k)).symm.norm_map _

/-- The actual charge-one evaluation tensor, in the existing Sym2 definition.
Its eventual identification with the periodized raw contact pair is pending. -/
def rawBosonPair (G : Geometry) (theta : Twist) (R : ℂ) : PhysicalSym2 G theta :=
  symTensor (evaluationKernel G theta 1 R) (evaluationKernel G theta 1 R)

private theorem rawTensorQ_evaluation (G : Geometry) (theta : Twist) (R : ℂ)
    (ψ : LLL G theta 1 ⊗[ℂ] LLL G theta 1) :
    (rawContactQ G theta ψ).val R =
      inner ℂ (evaluationKernel G theta 1 R ⊗ₜ[ℂ] evaluationKernel G theta 1 R) ψ := by
  induction ψ using TensorProduct.induction_on with
  | zero =>
    change (0 : ℂ) = inner ℂ _ (0 : LLL G theta 1 ⊗[ℂ] LLL G theta 1)
    simp
  | add ψ φ hψ hφ =>
    simp only [map_add, Submodule.coe_add, Pi.add_apply, inner_add_right, hψ, hφ]
  | tmul f g =>
    change f.val R * g.val R = _
    rw [TensorProduct.inner_tmul, evaluationKernel_reproduces, evaluationKernel_reproduces]

theorem contactQ_evaluation (G : Geometry) (theta : Twist)
    (ψ : PhysicalSym2 G theta) (R : ℂ) :
    (contactQ G theta ψ).val R = inner ℂ (rawBosonPair G theta R) ψ := by
  change (rawContactQ G theta ψ.val).val R =
    inner ℂ (symTensor (evaluationKernel G theta 1 R) (evaluationKernel G theta 1 R)).val ψ.val
  rw [rawTensorQ_evaluation, symTensor_same]

/-- The actual physical cell contact pair operator, with no eigenvalue
rescaling or unrelated budget. Its many-body lift is not defined here. -/
def bosonPairOperator (G : Geometry) (theta : Twist) :
    PhysicalSym2 G theta →L[ℂ] PhysicalSym2 G theta :=
  (contactQ G theta).adjoint.comp (contactQ G theta)

theorem bosonPairOperator_inner (G : Geometry) (theta : Twist)
    (ψ φ : PhysicalSym2 G theta) :
    inner ℂ ψ (bosonPairOperator G theta φ) =
      cellInner G 2 (contactQ G theta ψ).val (contactQ G theta φ).val := by
  change inner ℂ ψ ((contactQ G theta).adjoint (contactQ G theta φ)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, lll_inner_eq_cellInner]

theorem bosonPairOperator_contact_form (G : Geometry) (theta : Twist)
    (ψ φ : PhysicalSym2 G theta) :
    inner ℂ ψ (bosonPairOperator G theta φ) =
      ∫ R, conj (inner ℂ (rawBosonPair G theta R) ψ) *
        inner ℂ (rawBosonPair G theta R) φ ∂cellMeasure G 2 := by
  rw [bosonPairOperator_inner]
  unfold cellInner
  simp_rw [contactQ_evaluation]

theorem bosonPairOperator_self_nonneg (G : Geometry) (theta : Twist)
    (ψ : PhysicalSym2 G theta) :
    0 ≤ (inner ℂ ψ (bosonPairOperator G theta ψ)).re := by
  rw [bosonPairOperator_inner]
  exact cellInner_self_re_nonneg G 2 _

/-- Operator-kernel equality is for this exact physical pair operator.
No statement about a many-body H or its dimension is substituted. -/
theorem bosonPairOperator_ker (G : Geometry) (theta : Twist) :
    (bosonPairOperator G theta).ker = (contactQ G theta).ker :=
  ContinuousLinearMap.ker_adjoint_comp_self _

theorem bosonPairOperator_zero_iff_diagonal (G : Geometry) (theta : Twist)
    (ψ : PhysicalSym2 G theta) :
    bosonPairOperator G theta ψ = 0 ↔
      ∀ R, rawPairFunction G theta 1 1 ψ.val (R, R) = 0 := by
  change ψ ∈ (bosonPairOperator G theta).ker ↔ _
  rw [bosonPairOperator_ker]
  change rawContactQ G theta ψ.val = 0 ↔ _
  exact rawContactQ_eq_zero_iff G theta ψ.val

/-- Pointwise comparison relative to the same actual contact pair form.
The operator norm is a derived evaluation norm; its uniform geometric
estimate and identification with the paper's k₂ remain pending. -/
theorem boson_contact_evaluation_bound (G : Geometry) (theta : Twist)
    (ψ : PhysicalSym2 G theta) (R : ℂ) :
    ‖inner ℂ (rawBosonPair G theta R) ψ‖ ^ 2 ≤
      ‖lllEvaluation G theta 2 R‖ ^ 2 *
        (inner ℂ ψ (bosonPairOperator G theta ψ)).re := by
  have henergy : (inner ℂ ψ (bosonPairOperator G theta ψ)).re =
      ‖contactQ G theta ψ‖ ^ 2 := by
    rw [bosonPairOperator_inner, cellInner_self, Complex.ofReal_re]
    exact (lll_norm_sq_eq_cellIntegral G theta 2 (contactQ G theta ψ)).symm
  rw [← contactQ_evaluation, henergy]
  have h := lllEvaluation_bound G theta 2 R (contactQ G theta ψ)
  calc
    _ ≤ (‖lllEvaluation G theta 2 R‖ * ‖contactQ G theta ψ‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
    _ = _ := by ring

#print axioms contactQ
#print axioms contactQ_apply
#print axioms evaluationKernel
#print axioms evaluationKernel_reproduces
#print axioms evaluationKernel_norm
#print axioms rawBosonPair
#print axioms contactQ_evaluation
#print axioms bosonPairOperator
#print axioms bosonPairOperator_inner
#print axioms bosonPairOperator_contact_form
#print axioms bosonPairOperator_self_nonneg
#print axioms bosonPairOperator_ker
#print axioms bosonPairOperator_zero_iff_diagonal
#print axioms boson_contact_evaluation_bound

end TorusLean.Shared
