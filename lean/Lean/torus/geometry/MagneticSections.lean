import torus.geometry.LatticePhase
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Raw physical LLL sections and the full COM target

Source: `sections/02-geometry.tex`, the definition of `H_k(T)` following
`eq:translation` and the output of `eq:J-definition`.

These are actual functions on the universal cover, with an entire holomorphic
factor and the paper's boundary law. They are not finite coordinate vectors.
The cell inner product, nondegeneracy, completion, finite dimension `k*M`,
jet mapping theorem, and all-COM Gram formula remain separate obligations.
-/

set_option autoImplicit false

namespace TorusLean.Geometry

open scoped ComplexConjugate

noncomputable section

/-- The physical Gaussian factor `exp(-k*|z|^2/2)`. -/
def gaussianFactor (k : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(k : ℂ) * (z * conj z) / 2)

/-- Actual Gaussian-holomorphic functions; `Differentiable ℂ` globally means
the holomorphic factor is entire. No finite dimension is built into this. -/
def IsGaussianHolomorphic (k : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z, f z = gaussianFactor k z * F z

/-- Every lattice period has the charge power of the common single-particle
twist. The eigencharacter direction is fixed by the original paper. -/
def HasLatticeBoundary (M k : ℕ) (omega1 omega2 : ℂ)
    (theta1 theta2 : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ p : ℤ × ℤ,
    HasMagneticEigencharacter (k : ℝ) (latticePeriod omega1 omega2 p)
      (latticeChi M theta1 theta2 p ^ k) f

/-- Raw charge-`k` physical LLL sections, before equipping the cell norm.
Legal shared geometry will supply positive flux and its area equation. -/
def RawLLL (M k : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ) :=
  {f : ℂ → ℂ // IsGaussianHolomorphic (k : ℝ) f ∧
    HasLatticeBoundary M k omega1 omega2 theta1 theta2 f}

/-- Full COM output for a finite relative-jet index set. Each component is
the entire raw charge-`a+b` section space. No COM/orbital index is truncated. -/
def FullCOMTarget (D : Finset ℕ) (M a b : ℕ) (omega1 omega2 : ℂ)
    (theta1 theta2 : ℝ) :=
  (d : {d : ℕ // d ∈ D}) → RawLLL M (a + b) omega1 omega2 theta1 theta2

theorem gaussianHolomorphic_zero (k : ℝ) :
    IsGaussianHolomorphic k (0 : ℂ → ℂ) := by
  refine ⟨fun _ => 0, differentiable_const _, ?_⟩
  intro z
  simp

theorem gaussianHolomorphic_add (k : ℝ) (f g : ℂ → ℂ)
    (hf : IsGaussianHolomorphic k f) (hg : IsGaussianHolomorphic k g) :
    IsGaussianHolomorphic k (f + g) := by
  obtain ⟨F, hF, hf⟩ := hf
  obtain ⟨G, hG, hg⟩ := hg
  refine ⟨F + G, hF.add hG, ?_⟩
  intro z
  change f z + g z = gaussianFactor k z * (F z + G z)
  rw [hf, hg]
  ring

theorem gaussianHolomorphic_smul (k : ℝ) (c : ℂ) (f : ℂ → ℂ)
    (hf : IsGaussianHolomorphic k f) : IsGaussianHolomorphic k (c • f) := by
  obtain ⟨F, hF, hf⟩ := hf
  refine ⟨fun z => c * F z, hF.const_mul c, ?_⟩
  intro z
  change c * f z = gaussianFactor k z * (c * F z)
  rw [hf]
  ring

theorem latticeBoundary_zero (M k : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ) :
    HasLatticeBoundary M k omega1 omega2 theta1 theta2 (0 : ℂ → ℂ) := by
  intro p
  funext z
  simp [magneticTranslate]

theorem latticeBoundary_add (M k : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ)
    (f g : ℂ → ℂ) (hf : HasLatticeBoundary M k omega1 omega2 theta1 theta2 f)
    (hg : HasLatticeBoundary M k omega1 omega2 theta1 theta2 g) :
    HasLatticeBoundary M k omega1 omega2 theta1 theta2 (f + g) := by
  intro p
  funext z
  have hfp := congrFun (hf p) z
  have hgp := congrFun (hg p) z
  simp only [magneticTranslate] at hfp hgp
  change Complex.exp (magneticExponent (k : ℝ) z (latticePeriod omega1 omega2 p)) *
      (f (z - latticePeriod omega1 omega2 p) + g (z - latticePeriod omega1 omega2 p)) =
    latticeChi M theta1 theta2 p ^ k * (f z + g z)
  rw [mul_add, hfp, hgp, mul_add]

theorem latticeBoundary_smul (M k : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ)
    (c : ℂ) (f : ℂ → ℂ)
    (hf : HasLatticeBoundary M k omega1 omega2 theta1 theta2 f) :
    HasLatticeBoundary M k omega1 omega2 theta1 theta2 (c • f) := by
  intro p
  have hfp := hf p
  change magneticTranslate (k : ℝ) (latticePeriod omega1 omega2 p)
      (fun z => c * f z) = fun z => latticeChi M theta1 theta2 p ^ k * (c * f z)
  rw [magneticTranslate_const_mul, hfp]
  funext z
  ring

/-- Honest linear subspace of universal-cover functions. Root may use this
carrier for `Shared.LLL`; its metric/Hilbert structure still requires proof. -/
def rawLLLSubmodule (M k : ℕ) (omega1 omega2 : ℂ) (theta1 theta2 : ℝ) :
    Submodule ℂ (ℂ → ℂ) where
  carrier := {f | IsGaussianHolomorphic (k : ℝ) f ∧
    HasLatticeBoundary M k omega1 omega2 theta1 theta2 f}
  zero_mem' := ⟨gaussianHolomorphic_zero _, latticeBoundary_zero _ _ _ _ _ _⟩
  add_mem' := fun hf hg => ⟨gaussianHolomorphic_add _ _ _ hf.1 hg.1,
    latticeBoundary_add _ _ _ _ _ _ _ _ hf.2 hg.2⟩
  smul_mem' := fun c f hf => ⟨gaussianHolomorphic_smul _ c f hf.1,
    latticeBoundary_smul _ _ _ _ _ _ c f hf.2⟩

theorem gaussianFactor_eq_norm (k : ℝ) (z : ℂ) :
    gaussianFactor k z = Complex.exp (((-k * ‖z‖ ^ 2 / 2 : ℝ) : ℂ)) := by
  unfold gaussianFactor
  rw [Complex.mul_conj']
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

theorem gaussianFactor_ne_zero (k : ℝ) (z : ℂ) :
    gaussianFactor k z ≠ 0 :=
  Complex.exp_ne_zero _

/-- The raw holomorphic factor is unique, since the physical Gaussian
never vanishes. This does not assert a theta dimension theorem. -/
theorem gaussianFactor_factor_unique (k : ℝ) (F G : ℂ → ℂ)
    (h : ∀ z, gaussianFactor k z * F z = gaussianFactor k z * G z) : F = G := by
  funext z
  exact mul_left_cancel₀ (gaussianFactor_ne_zero k z) (h z)

theorem gaussian_translate_exponents (k : ℝ) (z x : ℂ) :
    magneticExponent k z x + -(k : ℂ) * ((z - x) * conj (z - x)) / 2 =
      -(k : ℂ) * (z * conj z) / 2 +
        (k : ℂ) * (z * conj x - (x * conj x) / 2) := by
  simp only [magneticExponent, map_sub]
  ring

/-- Genuine preservation of the physical differential condition under the
universal-cover magnetic translations, with no boundary assumptions. -/
theorem gaussianHolomorphic_translate (k : ℝ) (x : ℂ) (f : ℂ → ℂ)
    (hf : IsGaussianHolomorphic k f) :
    IsGaussianHolomorphic k (magneticTranslate k x f) := by
  obtain ⟨F, hF, hf⟩ := hf
  refine ⟨fun z => Complex.exp ((k : ℂ) * (z * conj x - (x * conj x) / 2)) *
      F (z - x), ?_, ?_⟩
  · have hlin : Differentiable ℂ (fun z : ℂ =>
        (k : ℂ) * (z * conj x - (x * conj x) / 2)) :=
      ((differentiable_id.mul_const (conj x)).sub_const ((x * conj x) / 2)).const_mul (k : ℂ)
    exact hlin.cexp.mul (hF.comp (differentiable_id.sub_const x))
  · intro z
    rw [magneticTranslate, hf, gaussianFactor, gaussianFactor, ← mul_assoc,
      ← Complex.exp_add]
    rw [gaussian_translate_exponents, Complex.exp_add]
    ring

/-- All-period forward boundary formula, retaining inverse chi. -/
theorem latticeBoundary_iff_forward (M k : ℕ) (omega1 omega2 : ℂ)
    (theta1 theta2 : ℝ) (f : ℂ → ℂ) :
    HasLatticeBoundary M k omega1 omega2 theta1 theta2 f ↔
      ∀ (p : ℤ × ℤ) (z : ℂ),
        f (z + latticePeriod omega1 omega2 p) =
          (latticeChi M theta1 theta2 p ^ k)⁻¹ *
            Complex.exp (magneticExponent (k : ℝ) z (latticePeriod omega1 omega2 p)) *
              f z := by
  unfold HasLatticeBoundary
  exact forall_congr' fun p => magneticEigencharacter_iff_forward _ _ _
    (pow_ne_zero k (latticeChi_ne_zero M theta1 theta2 p)) f

/-- The exact fractional lattice translations appearing in the full-COM
Gram formula preserve the same twist, on the entire raw section space.
No LLL dimension or COM mode cutoff is an input. -/
theorem latticeBoundary_fractional_translate (M a t : ℕ) (ht : 0 < t)
    (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (theta1 theta2 : ℝ) (q : ℤ × ℤ) (f : ℂ → ℂ)
    (hf : HasLatticeBoundary M t omega1 omega2 theta1 theta2 f) :
    HasLatticeBoundary M t omega1 omega2 theta1 theta2
      (magneticTranslate (t : ℝ)
        ((((a : ℝ) / (t : ℝ) : ℝ) : ℂ) * latticePeriod omega1 omega2 q) f) := by
  intro p
  exact magneticEigencharacter_translate _ _ _ _ f
    (fractionalLattice_cocycle_symmetric M a t ht omega1 omega2 harea p q) (hf p)

/-- Actual full-space map underlying the translations in `eq:exact-JJ`.
Its cell-inner-product unitarity remains a separate analytic obligation. -/
def rawLLLFractionalTranslate (M a t : ℕ) (ht : 0 < t) (omega1 omega2 : ℂ)
    (harea : latticeArea omega1 omega2 = Real.pi * (M : ℝ))
    (theta1 theta2 : ℝ) (q : ℤ × ℤ) :
    RawLLL M t omega1 omega2 theta1 theta2 →
      RawLLL M t omega1 omega2 theta1 theta2 :=
  fun f => ⟨magneticTranslate (t : ℝ)
    ((((a : ℝ) / (t : ℝ) : ℝ) : ℂ) * latticePeriod omega1 omega2 q) f.val,
      gaussianHolomorphic_translate _ _ _ f.property.1,
      latticeBoundary_fractional_translate M a t ht omega1 omega2 harea
        theta1 theta2 q f.val f.property.2⟩

#print axioms gaussianFactor_eq_norm
#print axioms gaussianHolomorphic_zero
#print axioms gaussianHolomorphic_add
#print axioms gaussianHolomorphic_smul
#print axioms latticeBoundary_zero
#print axioms latticeBoundary_add
#print axioms latticeBoundary_smul
#print axioms gaussianFactor_ne_zero
#print axioms gaussianFactor_factor_unique
#print axioms gaussian_translate_exponents
#print axioms gaussianHolomorphic_translate
#print axioms latticeBoundary_iff_forward
#print axioms latticeBoundary_fractional_translate

end

end TorusLean.Geometry
