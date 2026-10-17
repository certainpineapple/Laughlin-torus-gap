import torus.shared.BosonThreeBodyLift

/-!
# The paper's factorial polynomial coordinates inside the canonical Fock core

The polynomial variables of the rational certificate have single-orbital scale
`j!`. They are not the canonical creation variables. This file constructs their
actual canonical vectors by positive square-root rescaling and verifies their
Gram matrices and coefficient-matrix quadratic forms in the same `ip` used by
the normalized three-body lift. It does not assert the separate planar-to-torus
periodization identity or identify a certificate auxiliary operator with the
physical single-contraction operator.
-/

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators ComplexConjugate
open Matrix
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Orbital-factorial part, without the occupation-multiplicity factorials. -/
def orbitalWeight (scale : ι → ℕ) (n : ι →₀ ℕ) : ℕ :=
  ∏ i, scale i ^ n i

theorem occupationMetricWeight_factor (scale : ι → ℕ) (n : ι →₀ ℕ) :
    occupationMetricWeight scale n =
      occupationMetricWeight (fun _ : ι => 1) n * orbitalWeight scale n := by
  simp [occupationMetricWeight, orbitalWeight, Finset.prod_mul_distrib]

/-- The actual canonical polynomial corresponding to the paper's `x^n`. -/
def canonicalMonomial (scale : ι → ℕ) (n : ι →₀ ℕ) : Core ι ℂ :=
  MvPolynomial.monomial n (Real.sqrt (orbitalWeight scale n : ℝ) : ℂ)

/-- Orthogonality and the exact paper Gram factor, with no inverse Gram. -/
theorem canonicalMonomial_inner (scale : ι → ℕ) (n m : ι →₀ ℕ) :
    ip (canonicalMonomial scale n) (canonicalMonomial scale m) =
      if n = m then (occupationMetricWeight scale n : ℂ) else 0 := by
  classical
  by_cases h : n = m
  · subst m
    simp only [canonicalMonomial, ip, occupationInner_monomial_left,
      MvPolynomial.coeff_monomial, ite_true, Complex.star_def, Complex.conj_ofReal]
    rw [mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast,
      ← Nat.cast_mul, ← occupationMetricWeight_factor]
  · simp [canonicalMonomial, ip, occupationInner_monomial_left,
      MvPolynomial.coeff_monomial, h, Ne.symm h]

/-- Paper single-orbital factorial weights on an explicit finite orbital range. -/
def factorialScale (D : ℕ) (j : Fin (D + 1)) : ℕ := j.val.factorial

theorem factorialScale_pos (D : ℕ) (j : Fin (D + 1)) :
    0 < factorialScale D j := Nat.factorial_pos _

/-- The rational certificate's `prod n_j! (j!)^n_j` is the canonical inner product. -/
theorem factorialMonomial_inner (D : ℕ) (n m : Fin (D + 1) →₀ ℕ) :
    ip (canonicalMonomial (factorialScale D) n)
      (canonicalMonomial (factorialScale D) m) =
      if n = m then ((∏ j : Fin (D + 1), (n j).factorial * j.val.factorial ^ n j : ℕ) : ℂ)
        else 0 := by
  simpa [occupationMetricWeight, factorialScale] using
    canonicalMonomial_inner (factorialScale D) n m

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Synthesis of the actual scaled occupation vectors indexed by a finite block. -/
def canonicalBlock (scale : ι → ℕ) (occ : B → (ι →₀ ℕ)) (x : B → ℂ) : Core ι ℂ :=
  ∑ a, x a • canonicalMonomial scale (occ a)

/-- Every cross term is evaluated in the canonical inner product; distinct
occupation labels, not orthonormality, are the required basis hypothesis. -/
theorem canonicalBlock_inner (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hocc : Function.Injective occ) (x y : B → ℂ) :
    ip (canonicalBlock scale occ x) (canonicalBlock scale occ y) =
      ∑ a, (occupationMetricWeight scale (occ a) : ℂ) * star (x a) * y a := by
  simp only [canonicalBlock, inner_sum_left, inner_sum_right,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right, canonicalMonomial_inner]
  simp_rw [hocc.eq_iff]
  simp [mul_comm]

theorem canonicalBlock_basis_inner (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hocc : Function.Injective occ) (x : B → ℂ) (a : B) :
    ip (canonicalMonomial scale (occ a)) (canonicalBlock scale occ x) =
      (occupationMetricWeight scale (occ a) : ℂ) * x a := by
  simp only [canonicalBlock, inner_sum_right, TwoBodyLift.inner_smul_right,
    canonicalMonomial_inner]
  simp_rw [hocc.eq_iff]
  simp [mul_comm]

/-- Positive orbital scales give faithful, nonorthonormal paper coordinates. -/
theorem canonicalBlock_injective (scale : ι → ℕ) (hscale : ∀ i, 0 < scale i)
    (occ : B → (ι →₀ ℕ)) (hocc : Function.Injective occ) :
    Function.Injective (canonicalBlock scale occ) := by
  intro x y hxy
  funext a
  have he := congrArg (fun p => ip (canonicalMonomial scale (occ a)) p) hxy
  rw [canonicalBlock_basis_inner scale occ hocc,
    canonicalBlock_basis_inner scale occ hocc] at he
  have hg : (occupationMetricWeight scale (occ a) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (occupationMetricWeight_pos scale hscale _))
  exact mul_left_cancel₀ hg he

/-- A one-dimensional output block gives the actual row amplitude directly. -/
theorem canonicalBlock_row_action (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (out : ι →₀ ℕ) (F : Core ι ℂ →ₗ[ℂ] Core ι ℂ) (c : B → ℂ)
    (hF : ∀ b, F (canonicalMonomial scale (occ b)) =
      c b • canonicalMonomial scale out) (x : B → ℂ) :
    F (canonicalBlock scale occ x) =
      (∑ b, c b * x b) • canonicalMonomial scale out := by
  simp only [canonicalBlock, map_sum, map_smul, hF, smul_smul, Finset.sum_smul,
    mul_comm]

/-- This is the exact row-square matrix used by the three-particle rational
reconstruction: the output occupation metric multiplies the outer product. -/
theorem canonicalBlock_row_form (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (out : ι →₀ ℕ) (F : Core ι ℂ →ₗ[ℂ] Core ι ℂ) (c : B → ℂ)
    (hF : ∀ b, F (canonicalMonomial scale (occ b)) =
      c b • canonicalMonomial scale out) (x y : B → ℂ) :
    ip (F (canonicalBlock scale occ x)) (F (canonicalBlock scale occ y)) =
      star x ⬝ᵥ ((fun a b => (occupationMetricWeight scale out : ℂ) *
        star (c a) * c b) *ᵥ y) := by
  rw [canonicalBlock_row_action scale occ out F c hF,
    canonicalBlock_row_action scale occ out F c hF]
  simp only [TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
    canonicalMonomial_inner, ite_true, star_sum, star_mul,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem occupationMetricWeight_single (scale : ι → ℕ) (j : ι) :
    occupationMetricWeight scale (Finsupp.single j 1) = scale j := by
  have hz : occupationMetricWeight scale (0 : ι →₀ ℕ) = 1 := by
    simp [occupationMetricWeight]
  simpa [hz] using occupationMetricWeight_add_single scale (0 : ι →₀ ℕ) j

/-- For the row output `x_j`, the physical Gram weight is exactly `j!`. -/
theorem factorialSingle_weight (D : ℕ) (j : Fin (D + 1)) :
    occupationMetricWeight (factorialScale D) (Finsupp.single j 1) = j.val.factorial :=
  occupationMetricWeight_single (factorialScale D) j

/-- An actual polynomial operator with these basis coefficients acts by the
certificate coefficient matrix. The hypothesis is a concrete action identity,
not an assumed positivity or an assumed target bound. -/
theorem canonicalBlock_action (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (A : Core ι ℂ →ₗ[ℂ] Core ι ℂ) (M : Matrix B B ℂ)
    (hA : ∀ b, A (canonicalMonomial scale (occ b)) =
      ∑ a, M a b • canonicalMonomial scale (occ a)) (x : B → ℂ) :
    A (canonicalBlock scale occ x) = canonicalBlock scale occ (M *ᵥ x) := by
  simp only [canonicalBlock, map_sum, map_smul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]

/-- The paper form matrix is `G M`, with G on the row index. -/
def paperFormMatrix (scale : ι → ℕ) (occ : B → (ι →₀ ℕ)) (M : Matrix B B ℂ) :
    Matrix B B ℂ := fun a b => (occupationMetricWeight scale (occ a) : ℂ) * M a b

theorem canonicalBlock_operator_form (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hocc : Function.Injective occ) (A : Core ι ℂ →ₗ[ℂ] Core ι ℂ)
    (M : Matrix B B ℂ)
    (hA : ∀ b, A (canonicalMonomial scale (occ b)) =
      ∑ a, M a b • canonicalMonomial scale (occ a)) (x y : B → ℂ) :
    ip (canonicalBlock scale occ x) (A (canonicalBlock scale occ y)) =
      star x ⬝ᵥ (paperFormMatrix scale occ M *ᵥ y) := by
  rw [canonicalBlock_action scale occ A M hA, canonicalBlock_inner scale occ hocc]
  simp only [paperFormMatrix, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The same concrete vector as an element of the existing complete N=3 core. -/
def canonicalThreeMonomial (scale : ι → ℕ) (n : ι →₀ ℕ) (hn : n.degree = 3) :
    ThreeSector ι :=
  ⟨canonicalMonomial scale n, MvPolynomial.isHomogeneous_monomial _ hn⟩

def canonicalThreeBlock (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hdegree : ∀ a, (occ a).degree = 3) (x : B → ℂ) : ThreeSector ι :=
  ∑ a, x a • canonicalThreeMonomial scale (occ a) (hdegree a)

theorem canonicalThreeBlock_val (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hdegree : ∀ a, (occ a).degree = 3) (x : B → ℂ) :
    (canonicalThreeBlock scale occ hdegree x).val = canonicalBlock scale occ x := by
  simp only [canonicalThreeBlock, Submodule.coe_sum, Submodule.coe_smul,
    canonicalThreeMonomial, canonicalBlock]

/-- A matrix statement in the paper coordinates is evaluated on actual vectors
of the same N=3 carrier consumed by `threeBodyLift`. -/
theorem canonicalThreeBlock_inner (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hocc : Function.Injective occ) (hdegree : ∀ a, (occ a).degree = 3)
    (x y : B → ℂ) :
    ip (canonicalThreeBlock scale occ hdegree x).val
      (canonicalThreeBlock scale occ hdegree y).val =
      ∑ a, (occupationMetricWeight scale (occ a) : ℂ) * star (x a) * y a := by
  rw [canonicalThreeBlock_val, canonicalThreeBlock_val]
  exact canonicalBlock_inner scale occ hocc x y

theorem canonicalThreeBlock_action (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hdegree : ∀ a, (occ a).degree = 3)
    (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι) (M : Matrix B B ℂ)
    (hA : ∀ b, A (canonicalThreeMonomial scale (occ b) (hdegree b)) =
      ∑ a, M a b • canonicalThreeMonomial scale (occ a) (hdegree a)) (x : B → ℂ) :
    A (canonicalThreeBlock scale occ hdegree x) =
      canonicalThreeBlock scale occ hdegree (M *ᵥ x) := by
  simp only [canonicalThreeBlock, map_sum, map_smul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]

theorem canonicalThreeBlock_operator_form (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hocc : Function.Injective occ) (hdegree : ∀ a, (occ a).degree = 3)
    (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι) (M : Matrix B B ℂ)
    (hA : ∀ b, A (canonicalThreeMonomial scale (occ b) (hdegree b)) =
      ∑ a, M a b • canonicalThreeMonomial scale (occ a) (hdegree a)) (x y : B → ℂ) :
    ip (canonicalThreeBlock scale occ hdegree x).val
      (A (canonicalThreeBlock scale occ hdegree y)).val =
      star x ⬝ᵥ (paperFormMatrix scale occ M *ᵥ y) := by
  rw [canonicalThreeBlock_action scale occ hdegree A M hA,
    canonicalThreeBlock_inner scale occ hocc]
  simp only [paperFormMatrix, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Exact compatibility with the frozen normalized three-body lift on N=3.
No extra 3! is introduced when converting the paper coefficient matrix to its
actual canonical three-particle quadratic form. -/
theorem canonicalThreeBlock_lift_form (scale : ι → ℕ) (occ : B → (ι →₀ ℕ))
    (hocc : Function.Injective occ) (hdegree : ∀ a, (occ a).degree = 3)
    (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι) (M : Matrix B B ℂ)
    (hA : ∀ b, A (canonicalThreeMonomial scale (occ b) (hdegree b)) =
      ∑ a, M a b • canonicalThreeMonomial scale (occ a) (hdegree a)) (x y : B → ℂ) :
    ip (canonicalThreeBlock scale occ hdegree x).val
      (threeBodyLift A (canonicalThreeBlock scale occ hdegree y).val) =
      star x ⬝ᵥ (paperFormMatrix scale occ M *ᵥ y) := by
  rw [threeBodyLift_threeSector]
  exact canonicalThreeBlock_operator_form scale occ hocc hdegree A M hA x y

#print axioms canonicalMonomial_inner
#print axioms factorialMonomial_inner
#print axioms canonicalBlock_inner
#print axioms canonicalBlock_injective
#print axioms canonicalBlock_action
#print axioms canonicalBlock_row_form
#print axioms factorialSingle_weight
#print axioms canonicalBlock_operator_form
#print axioms canonicalThreeBlock_inner
#print axioms canonicalThreeBlock_operator_form
#print axioms canonicalThreeBlock_lift_form

end TorusLean.Shared.BosonFiniteCertificateCoordinate
