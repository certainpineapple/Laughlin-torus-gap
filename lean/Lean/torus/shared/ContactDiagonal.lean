import torus.shared.Geometry
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The actual raw contact diagonal

This constructs multiplication of the Gaussian-holomorphic sections with the
paper's all-period magnetic boundary law. The domain is the algebraic tensor
product of the actual raw section modules, and the codomain is the entire raw
charge-two section module. No finite orbital model or coherent family is an
input. The cell Hilbert structure, boundedness, Riesz kernels, adjoint, contact
frame and many-particle Hamiltonian remain separate obligations.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Geometry

open scoped ComplexConjugate

theorem gaussianFactor_add_charge (a b : ℝ) (z : ℂ) :
    gaussianFactor (a + b) z = gaussianFactor a z * gaussianFactor b z := by
  unfold gaussianFactor
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_add]
  ring

/-- Multiplication of the actual holomorphic factors adds physical charge. -/
theorem gaussianHolomorphic_mul_charge (a b : ℝ) (f g : ℂ → ℂ)
    (hf : IsGaussianHolomorphic a f) (hg : IsGaussianHolomorphic b g) :
    IsGaussianHolomorphic (a + b) (fun z => f z * g z) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  refine ⟨fun z => F z * G z, hF.mul hG, ?_⟩
  intro z
  change f z * g z = gaussianFactor (a + b) z * (F z * G z)
  rw [hf, hg, gaussianFactor_add_charge]
  ring

theorem magneticExponent_add_charge (a b : ℝ) (z x : ℂ) :
    magneticExponent (a + b) z x =
      magneticExponent a z x + magneticExponent b z x := by
  simp only [magneticExponent, Complex.ofReal_add]
  ring

/-- A simultaneous magnetic translation of the product has the sum charge. -/
theorem magneticTranslate_mul_charge (a b : ℝ) (x : ℂ) (f g : ℂ → ℂ) :
    magneticTranslate (a + b) x (fun z => f z * g z) =
      fun z => magneticTranslate a x f z * magneticTranslate b x g z := by
  funext z
  simp only [magneticTranslate, magneticExponent_add_charge, Complex.exp_add]
  ring

/-- Every lattice period is retained, with the power of the same chi.
The magnetic eigencharacter convention is not inverted. -/
theorem latticeBoundary_mul_charge (M a b : ℕ) (omega1 omega2 : ℂ)
    (theta1 theta2 : ℝ) (f g : ℂ → ℂ)
    (hf : HasLatticeBoundary M a omega1 omega2 theta1 theta2 f)
    (hg : HasLatticeBoundary M b omega1 omega2 theta1 theta2 g) :
    HasLatticeBoundary M (a + b) omega1 omega2 theta1 theta2
      (fun z => f z * g z) := by
  intro p
  unfold HasMagneticEigencharacter
  rw [Nat.cast_add, magneticTranslate_mul_charge]
  funext z
  rw [congrFun (hf p) z, congrFun (hg p) z, pow_add]
  ring

end TorusLean.Geometry

namespace TorusLean.Shared

open TorusLean.Geometry
open scoped TensorProduct

/-- The existing rawLLLSubmodule carrier with its algebraic module structure.
This is the actual universal-cover section type, before a cell norm is proved. -/
abbrev RawLLLModule (G : Geometry) (theta : Twist) (k : ℕ) :=
  ↥(rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2)

/-- The actual pointwise product of two sections, with the whole charge-a+b
section space as codomain. Surjectivity is not asserted. -/
def rawSectionProduct (G : Geometry) (theta : Twist) (a b : ℕ)
    (f : RawLLLModule G theta a) (g : RawLLLModule G theta b) :
    RawLLLModule G theta (a + b) :=
  ⟨fun z => f.val z * g.val z,
    by
      constructor
      · simpa only [Nat.cast_add] using
          gaussianHolomorphic_mul_charge (a : ℝ) (b : ℝ) f.val g.val
            f.property.1 g.property.1
      · exact latticeBoundary_mul_charge G.M a b G.omega1 G.omega2
          theta.theta1 theta.theta2 f.val g.val f.property.2 g.property.2⟩

@[simp]
theorem rawSectionProduct_apply (G : Geometry) (theta : Twist) (a b : ℕ)
    (f : RawLLLModule G theta a) (g : RawLLLModule G theta b) (R : ℂ) :
    (rawSectionProduct G theta a b f g).val R = f.val R * g.val R := rfl

/-- Multiplication is complex bilinear on the actual raw section modules. -/
def rawSectionMul (G : Geometry) (theta : Twist) (a b : ℕ) :
    RawLLLModule G theta a →ₗ[ℂ]
      RawLLLModule G theta b →ₗ[ℂ] RawLLLModule G theta (a + b) :=
  LinearMap.mk₂ ℂ (rawSectionProduct G theta a b)
    (by
      intro f₁ f₂ g
      apply Subtype.ext
      funext R
      change (f₁.val R + f₂.val R) * g.val R =
        f₁.val R * g.val R + f₂.val R * g.val R
      ring)
    (by
      intro c f g
      apply Subtype.ext
      funext R
      change (c * f.val R) * g.val R = c * (f.val R * g.val R)
      ring)
    (by
      intro f g₁ g₂
      apply Subtype.ext
      funext R
      change f.val R * (g₁.val R + g₂.val R) =
        f.val R * g₁.val R + f.val R * g₂.val R
      ring)
    (by
      intro c f g
      apply Subtype.ext
      funext R
      change f.val R * (c * g.val R) = c * (f.val R * g.val R)
      ring)

@[simp]
theorem rawSectionMul_apply (G : Geometry) (theta : Twist) (a b : ℕ)
    (f : RawLLLModule G theta a) (g : RawLLLModule G theta b) (R : ℂ) :
    (rawSectionMul G theta a b f g).val R = f.val R * g.val R := rfl

/-- The universal-property extension of the actual product to algebraic
tensors. This does not assert a Hilbert tensor completion or boundedness. -/
def rawProductQ (G : Geometry) (theta : Twist) (a b : ℕ) :
    RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b →ₗ[ℂ]
      RawLLLModule G theta (a + b) :=
  TensorProduct.lift (rawSectionMul G theta a b)

@[simp]
theorem rawProductQ_tmul_apply (G : Geometry) (theta : Twist) (a b : ℕ)
    (f : RawLLLModule G theta a) (g : RawLLLModule G theta b) (R : ℂ) :
    (rawProductQ G theta a b (f ⊗ₜ[ℂ] g)).val R = f.val R * g.val R := rfl

/-- The same algebraic pair tensor as a genuine two-point cover function.
No injectivity or pair-Hilbert norm is claimed by this map. -/
def rawPairFunction (G : Geometry) (theta : Twist) (a b : ℕ) :
    RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b →ₗ[ℂ]
      (ℂ × ℂ → ℂ) :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ
    (fun (f : RawLLLModule G theta a) (g : RawLLLModule G theta b)
      (z : ℂ × ℂ) => f.val z.1 * g.val z.2)
    (by
      intro f₁ f₂ g
      funext z
      change (f₁.val z.1 + f₂.val z.1) * g.val z.2 =
        f₁.val z.1 * g.val z.2 + f₂.val z.1 * g.val z.2
      ring)
    (by
      intro c f g
      funext z
      change (c * f.val z.1) * g.val z.2 = c * (f.val z.1 * g.val z.2)
      ring)
    (by
      intro f g₁ g₂
      funext z
      change f.val z.1 * (g₁.val z.2 + g₂.val z.2) =
        f.val z.1 * g₁.val z.2 + f.val z.1 * g₂.val z.2
      ring)
    (by
      intro c f g
      funext z
      change f.val z.1 * (c * g.val z.2) = c * (f.val z.1 * g.val z.2)
      ring)

@[simp]
theorem rawPairFunction_tmul_apply (G : Geometry) (theta : Twist) (a b : ℕ)
    (f : RawLLLModule G theta a) (g : RawLLLModule G theta b) (z : ℂ × ℂ) :
    rawPairFunction G theta a b (f ⊗ₜ[ℂ] g) z = f.val z.1 * g.val z.2 := rfl

/-- Literal restriction of a two-point cover function to its diagonal. -/
def coverDiagonal : (ℂ × ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun F R := F (R, R)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equality of actual cover functions on every algebraic tensor, not just
a formula on a pure-tensor input. -/
theorem rawProductQ_eq_diagonal (G : Geometry) (theta : Twist) (a b : ℕ) :
    (rawLLLSubmodule G.M (a + b) G.omega1 G.omega2
      theta.theta1 theta.theta2).subtype.comp (rawProductQ G theta a b) =
      coverDiagonal.comp (rawPairFunction G theta a b) := by
  apply TensorProduct.ext'
  intro f g
  rfl

theorem rawProductQ_apply_eq_diagonal (G : Geometry) (theta : Twist) (a b : ℕ)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta b) (R : ℂ) :
    (rawProductQ G theta a b ψ).val R = rawPairFunction G theta a b ψ (R, R) :=
  congrFun (LinearMap.congr_fun (rawProductQ_eq_diagonal G theta a b) ψ) R

/-- The raw physical contact diagonal, charge one times charge one to the
full charge-two raw LLL. This is the algebraic/analytic stage of Q. -/
def rawContactQ (G : Geometry) (theta : Twist) :
    RawLLLModule G theta 1 ⊗[ℂ] RawLLLModule G theta 1 →ₗ[ℂ]
      RawLLLModule G theta 2 :=
  rawProductQ G theta 1 1

@[simp]
theorem rawContactQ_tmul_apply (G : Geometry) (theta : Twist)
    (f g : RawLLLModule G theta 1) (R : ℂ) :
    (rawContactQ G theta (f ⊗ₜ[ℂ] g)).val R = f.val R * g.val R := rfl

theorem rawContactQ_apply_eq_diagonal (G : Geometry) (theta : Twist)
    (ψ : RawLLLModule G theta 1 ⊗[ℂ] RawLLLModule G theta 1) (R : ℂ) :
    (rawContactQ G theta ψ).val R = rawPairFunction G theta 1 1 ψ (R, R) :=
  rawProductQ_apply_eq_diagonal G theta 1 1 ψ R

/-- No COM component is discarded: the output satisfies the actual entire
factor condition on the universal cover. -/
theorem rawContactQ_gaussianHolomorphic (G : Geometry) (theta : Twist)
    (ψ : RawLLLModule G theta 1 ⊗[ℂ] RawLLLModule G theta 1) :
    IsGaussianHolomorphic (2 : ℝ) (rawContactQ G theta ψ).val :=
  (rawContactQ G theta ψ).property.1

/-- The output carries chi^2 for every integer lattice period. -/
theorem rawContactQ_latticeBoundary (G : Geometry) (theta : Twist)
    (ψ : RawLLLModule G theta 1 ⊗[ℂ] RawLLLModule G theta 1) :
    HasLatticeBoundary G.M 2 G.omega1 G.omega2 theta.theta1 theta.theta2
      (rawContactQ G theta ψ).val :=
  (rawContactQ G theta ψ).property.2

/-- Exchanging the two charge-one factors leaves the actual diagonal fixed.
This theorem does not introduce a competing Sym2 space or norm. -/
theorem rawContactQ_comp_flip (G : Geometry) (theta : Twist) :
    (rawContactQ G theta).comp
      (TensorProduct.comm ℂ (RawLLLModule G theta 1)
        (RawLLLModule G theta 1)).toLinearMap = rawContactQ G theta := by
  apply TensorProduct.ext'
  intro f g
  apply Subtype.ext
  funext R
  change g.val R * f.val R = f.val R * g.val R
  exact mul_comm _ _

theorem rawContactQ_flip (G : Geometry) (theta : Twist)
    (ψ : RawLLLModule G theta 1 ⊗[ℂ] RawLLLModule G theta 1) :
    rawContactQ G theta
      ((TensorProduct.comm ℂ (RawLLLModule G theta 1)
        (RawLLLModule G theta 1)) ψ) = rawContactQ G theta ψ :=
  LinearMap.congr_fun (rawContactQ_comp_flip G theta) ψ

/-- The raw contact kernel is precisely vanishing of the actual diagonal.
Identification with the kernel of a positive cell contact H is still open. -/
theorem rawContactQ_eq_zero_iff (G : Geometry) (theta : Twist)
    (ψ : RawLLLModule G theta 1 ⊗[ℂ] RawLLLModule G theta 1) :
    rawContactQ G theta ψ = 0 ↔
      ∀ R : ℂ, rawPairFunction G theta 1 1 ψ (R, R) = 0 := by
  constructor
  · intro h R
    rw [← rawContactQ_apply_eq_diagonal, h]
    rfl
  · intro h
    apply Subtype.ext
    funext R
    change (rawContactQ G theta ψ).val R = 0
    rw [rawContactQ_apply_eq_diagonal]
    exact h R

#print axioms TorusLean.Geometry.gaussianFactor_add_charge
#print axioms TorusLean.Geometry.gaussianHolomorphic_mul_charge
#print axioms TorusLean.Geometry.magneticExponent_add_charge
#print axioms TorusLean.Geometry.magneticTranslate_mul_charge
#print axioms TorusLean.Geometry.latticeBoundary_mul_charge
#print axioms rawSectionProduct
#print axioms rawSectionProduct_apply
#print axioms rawSectionMul
#print axioms rawSectionMul_apply
#print axioms rawProductQ
#print axioms rawProductQ_tmul_apply
#print axioms rawPairFunction
#print axioms rawPairFunction_tmul_apply
#print axioms coverDiagonal
#print axioms rawProductQ_eq_diagonal
#print axioms rawProductQ_apply_eq_diagonal
#print axioms rawContactQ
#print axioms rawContactQ_tmul_apply
#print axioms rawContactQ_apply_eq_diagonal
#print axioms rawContactQ_gaussianHolomorphic
#print axioms rawContactQ_latticeBoundary
#print axioms rawContactQ_comp_flip
#print axioms rawContactQ_flip
#print axioms rawContactQ_eq_zero_iff

end TorusLean.Shared

end
