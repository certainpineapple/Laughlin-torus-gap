import torus.shared.PhysicalBosonSector
import torus.shared.ContactFrame

/-!
# Actual particle-pair diagonal in the same physical contact measure

The canonical particle pair is literally restricted to `(R,R)` while all
remaining particle coordinates are retained. The target measure is the
original charge-two cell measure times the original spectator product
measure. This does not define the diagonal by transporting a polynomial
annihilator, and does not assume a many-body lift identity.

The labeled-product Gram matrix below already uses the same physical
`bosonPairOperator = contactQ.adjoint ∘ contactQ`. Identifying its sum over
particle pairs with the existing normal-ordered lift on symmetric occupation
functions still requires the permutation/removal counting step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace TorusLean.Shared.PhysicalBosonDiagonal

open MeasureTheory TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.PhysicalBosonSector
open scoped BigOperators ComplexConjugate

abbrev ContactConfiguration (N : ℕ) := ℂ × Configuration N

instance sectorMeasure_finite (G : Geometry) (N : ℕ) :
    IsFiniteMeasure (sectorMeasure G N) := by
  unfold sectorMeasure
  infer_instance

/-- Collapse two actual particle coordinates and keep every spectator. -/
def insertDiagonal (N : ℕ) (x : ContactConfiguration N) : Configuration (N + 2) :=
  Fin.cons x.1 (Fin.cons x.1 x.2)

def diagonalMap (N : ℕ) :
    (Configuration (N + 2) → ℂ) →ₗ[ℂ] (ContactConfiguration N → ℂ) where
  toFun F x := F (insertDiagonal N x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original mu_2 contact measure, with mu_1 in every spectator slot. -/
def contactMeasure (G : Geometry) (N : ℕ) : Measure (ContactConfiguration N) :=
  (cellMeasure G 2).prod (sectorMeasure G N)

def contactInner (G : Geometry) (N : ℕ)
    (F H : ContactConfiguration N → ℂ) : ℂ :=
  ∫ x, conj (F x) * H x ∂contactMeasure G N

def tailWord (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta (N + 2)) : Word G theta N :=
  fun a => w a.succ.succ

def pairProduct (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (R : ℂ) : ℂ :=
  (orbitalBasis G theta i).val R * (orbitalBasis G theta j).val R

theorem diagonal_wordFunction (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta (N + 2)) (x : ContactConfiguration N) :
    diagonalMap N (wordFunction G theta (N + 2) w) x =
      pairProduct G theta (w 0) (w 1) x.1 *
        wordFunction G theta N (tailWord G theta N w) x.2 := by
  change wordFunction G theta (N + 2) w (insertDiagonal N x) = _
  simp only [insertDiagonal, wordFunction, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one, tailWord, pairProduct]
  ring

theorem pairProduct_continuous (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) : Continuous (pairProduct G theta i j) :=
  (rawLLL_continuous G theta 1 (orbitalBasis G theta i)).mul
    (rawLLL_continuous G theta 1 (orbitalBasis G theta j))

theorem pairProduct_integrable (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) :
    Integrable (pairProduct G theta i j) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2 (pairProduct_continuous G theta i j)

theorem diagonal_wordFunction_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta (N + 2)) :
    Integrable (diagonalMap N (wordFunction G theta (N + 2) w))
      (contactMeasure G N) := by
  have h := Integrable.mul_prod (pairProduct_integrable G theta (w 0) (w 1))
    (wordFunction_integrable G theta N (tailWord G theta N w))
  have heq : diagonalMap N (wordFunction G theta (N + 2) w) =
      fun x => pairProduct G theta (w 0) (w 1) x.1 *
        wordFunction G theta N (tailWord G theta N w) x.2 :=
    funext (diagonal_wordFunction G theta N w)
  rw [heq]
  exact h

/-- The labeled diagonal Gram integral factors in the actual physical measures. -/
theorem diagonal_wordFunction_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta (N + 2)) :
    contactInner G N (diagonalMap N (wordFunction G theta (N + 2) w))
      (diagonalMap N (wordFunction G theta (N + 2) v)) =
      cellInner G 2 (pairProduct G theta (w 0) (w 1))
        (pairProduct G theta (v 0) (v 1)) *
          (if tailWord G theta N w = tailWord G theta N v then 1 else 0) := by
  classical
  have hF := integral_prod_mul
    (μ := cellMeasure G 2) (ν := sectorMeasure G N)
    (fun R => conj (pairProduct G theta (w 0) (w 1) R) *
      pairProduct G theta (v 0) (v 1) R)
    (fun y => conj (wordFunction G theta N (tailWord G theta N w) y) *
      wordFunction G theta N (tailWord G theta N v) y)
  calc
    _ = cellInner G 2 (pairProduct G theta (w 0) (w 1))
        (pairProduct G theta (v 0) (v 1)) *
          sectorInner G N (wordFunction G theta N (tailWord G theta N w))
            (wordFunction G theta N (tailWord G theta N v)) := by
      unfold contactInner
      simp only [diagonal_wordFunction, map_mul]
      simp_rw [show ∀ x : ContactConfiguration N,
        conj (pairProduct G theta (w 0) (w 1) x.1) *
            conj (wordFunction G theta N (tailWord G theta N w) x.2) *
              (pairProduct G theta (v 0) (v 1) x.1 *
                wordFunction G theta N (tailWord G theta N v) x.2) =
          (conj (pairProduct G theta (w 0) (w 1) x.1) *
            pairProduct G theta (v 0) (v 1) x.1) *
          (conj (wordFunction G theta N (tailWord G theta N w) x.2) *
            wordFunction G theta N (tailWord G theta N v) x.2) by intro x; ring]
      exact hF
    _ = _ := by rw [wordFunction_inner]

/-- The actual physical pair diagonal of a symmetrized basis tensor. -/
theorem contactQ_basis_symTensor (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) :
    (contactQ G theta (symTensor (orbitalBasis G theta i)
      (orbitalBasis G theta j))).val = pairProduct G theta i j := by
  funext R
  rw [contactQ_evaluation]
  change inner ℂ
    (symTensor (evaluationKernel G theta 1 R) (evaluationKernel G theta 1 R))
    (symTensor (orbitalBasis G theta i) (orbitalBasis G theta j)) = _
  rw [symTensor_inner, evaluationKernel_reproduces, evaluationKernel_reproduces]
  unfold pairProduct
  ring

/-- This is the original h=Q†Q coefficient, with no eigenvalue rescaling. -/
theorem pairProduct_inner_same_h (G : Geometry) (theta : Twist)
    (i j p q : OrbitalIndex G theta) :
    cellInner G 2 (pairProduct G theta i j) (pairProduct G theta p q) =
      inner ℂ (symTensor (orbitalBasis G theta i) (orbitalBasis G theta j))
        (bosonPairOperator G theta
          (symTensor (orbitalBasis G theta p) (orbitalBasis G theta q))) := by
  rw [bosonPairOperator_inner, contactQ_basis_symTensor, contactQ_basis_symTensor]

/-- Actual labeled contact diagonal and untouched spectators, for every N,
already have the same physical h=Q†Q Gram coefficients. -/
theorem diagonal_wordFunction_inner_same_h (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta (N + 2)) :
    contactInner G N (diagonalMap N (wordFunction G theta (N + 2) w))
      (diagonalMap N (wordFunction G theta (N + 2) v)) =
      inner ℂ (symTensor (orbitalBasis G theta (w 0)) (orbitalBasis G theta (w 1)))
        (bosonPairOperator G theta
          (symTensor (orbitalBasis G theta (v 0)) (orbitalBasis G theta (v 1)))) *
            (if tailWord G theta N w = tailWord G theta N v then 1 else 0) := by
  rw [diagonal_wordFunction_inner, pairProduct_inner_same_h]

/-- The N=2 member of the all-N construction agrees pointwise with the
unchanged physical contact Q after the accepted Fock factor 1/sqrt(2). -/
theorem diagonal_normalized_occupation_two (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (x : ContactConfiguration 0) :
    diagonalMap 0
      (fun z => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        occupationFunction G theta 2 (Finsupp.single i 1 + Finsupp.single j 1) z) x =
      (contactQ G theta (symTensor (orbitalBasis G theta i)
        (orbitalBasis G theta j))).val x.1 := by
  change (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
    occupationFunction G theta 2 (Finsupp.single i 1 + Finsupp.single j 1)
      (insertDiagonal 0 x) = _
  rw [occupationFunction_two_symTensor, contactQ_apply]
  simp only [insertDiagonal, Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
  have hnR : (Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hnC : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hnR
  rw [← mul_assoc, Complex.ofReal_inv,
    inv_mul_cancel₀ hnC, one_mul]

end TorusLean.Shared.PhysicalBosonDiagonal
