import torus.shared.Geometry
import ThetaSectionSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A concrete injection of physical LLL sections into analytic theta sections

The domain is the existing submodule of actual universal-cover functions with
the physical Gaussian-holomorphic condition and all-period magnetic boundary
law.  The map removes the nonvanishing Gaussian, scales by the first lattice
generator, and applies the explicit quadratic holomorphic gauge.  Its target
is the previously classified space of genuine entire theta sections.

No dimension, inner product, frame, Hamiltonian, or kernel is an input.  This
module proves finite dimension and an upper bound; it does not prove that the
injection is onto, a cell-inner-product isometry, or a Hamiltonian gap.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared

open scoped ComplexConjugate
open TorusLean.Geometry

/-- The actual lattice modulus, rather than an independent geometric input. -/
def thetaTau (G : Geometry) : ℂ := G.omega2 / G.omega1

/-- Quadratic gauge coefficient for charge `k`. -/
def thetaAlpha (G : Geometry) (k : ℕ) : ℂ :=
  (k : ℂ) * G.omega1 * conj G.omega1 / 2

/-- The inverse eigencharacter in the first forward boundary law. -/
def thetaSigma (theta : Twist) (k : ℕ) : ℂ :=
  -((k : ℂ) * (theta.theta1 : ℂ)) / (2 * (Real.pi : ℂ))

/-- The inverse eigencharacter in the second forward boundary law. -/
def thetaPsi (theta : Twist) (k : ℕ) : ℂ :=
  -(k : ℂ) * (theta.theta2 : ℂ)

theorem geometry_omega1_ne_zero (G : Geometry) : G.omega1 ≠ 0 := by
  intro h
  have ha := G.area
  rw [h] at ha
  simp only [map_zero, zero_mul, Complex.zero_im] at ha
  have hM : 0 < (G.M : ℝ) := by exact_mod_cast G.flux_pos
  exact (ne_of_gt (mul_pos Real.pi_pos hM)) ha.symm

theorem omega1_mul_thetaTau (G : Geometry) :
    G.omega1 * thetaTau G = G.omega2 := by
  unfold thetaTau
  field_simp [geometry_omega1_ne_zero G]
  <;> ring

theorem thetaTau_im_pos (G : Geometry) : 0 < (thetaTau G).im := by
  have hn : G.omega2.im * G.omega1.re - G.omega2.re * G.omega1.im =
      Real.pi * (G.M : ℝ) := by
    calc
      _ = (conj G.omega1 * G.omega2).im := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      _ = _ := G.area
  unfold thetaTau
  rw [Complex.div_im, ← sub_div, hn]
  exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast G.flux_pos))
    (Complex.normSq_pos.mpr (geometry_omega1_ne_zero G))

/-- The orientation/sign used in the second theta boundary exponent. -/
theorem geometry_cross_eq_flux (G : Geometry) :
    G.omega1 * conj G.omega2 - G.omega2 * conj G.omega1 =
      -2 * ((Real.pi : ℂ) * (G.M : ℂ)) * Complex.I := by
  have ha := G.area
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at ha
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    <;> ring
  · simp [Complex.mul_re, Complex.mul_im]
    <;> nlinarith

theorem thetaSigma_exponent (theta : Twist) (k : ℕ) :
    2 * (Real.pi : ℂ) * Complex.I * thetaSigma theta k =
      -(k : ℂ) * (theta.theta1 : ℂ) * Complex.I := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold thetaSigma
  field_simp [hpi]
  <;> ring

/-- Canonical entire factor; no choice of a witness is built into this map. -/
def holomorphicPart (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => f z / gaussianFactor (k : ℝ) z

theorem gaussianFactor_holomorphicPart (k : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    gaussianFactor (k : ℝ) z * holomorphicPart k f z = f z := by
  simp [holomorphicPart, div_eq_mul_inv, gaussianFactor_ne_zero,
    mul_comm, mul_left_comm, mul_assoc]

theorem holomorphicPart_eq_factor (k : ℕ) (f F : ℂ → ℂ)
    (hf : ∀ z, f z = gaussianFactor (k : ℝ) z * F z) :
    holomorphicPart k f = F := by
  funext z
  apply (div_eq_iff (gaussianFactor_ne_zero (k : ℝ) z)).2
  rw [hf z]
  ring

theorem holomorphicPart_differentiable (k : ℕ) (f : ℂ → ℂ)
    (hf : IsGaussianHolomorphic (k : ℝ) f) :
    Differentiable ℂ (holomorphicPart k f) := by
  obtain ⟨F, hF, hf⟩ := hf
  rw [holomorphicPart_eq_factor k f F hf]
  exact hF

theorem gaussian_forward_exponents (k : ℝ) (z x : ℂ) :
    magneticExponent k z x + -(k : ℂ) * (z * conj z) / 2 =
      -(k : ℂ) * ((z + x) * conj (z + x)) / 2 +
        (k : ℂ) * (z * conj x + x * conj x / 2) := by
  simp only [magneticExponent, map_add]
  ring

/-- Strip the actual Gaussian from the all-period physical forward law. -/
theorem holomorphicPart_forward (G : Geometry) (theta : Twist) (k : ℕ)
    (f : ℂ → ℂ)
    (hf : HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 f)
    (p : ℤ × ℤ) (z : ℂ) :
    holomorphicPart k f (z + latticePeriod G.omega1 G.omega2 p) =
      (latticeChi G.M theta.theta1 theta.theta2 p ^ k)⁻¹ *
        Complex.exp ((k : ℂ) *
          (z * conj (latticePeriod G.omega1 G.omega2 p) +
            latticePeriod G.omega1 G.omega2 p *
              conj (latticePeriod G.omega1 G.omega2 p) / 2)) *
        holomorphicPart k f z := by
  let x := latticePeriod G.omega1 G.omega2 p
  let c := (latticeChi G.M theta.theta1 theta.theta2 p ^ k)⁻¹
  have hg : magneticExponent (k : ℝ) z x + -(k : ℂ) * (z * conj z) / 2 =
      -(k : ℂ) * ((z + x) * conj (z + x)) / 2 +
        (k : ℂ) * (z * conj x + x * conj x / 2) := by
    simpa only [Complex.ofReal_natCast] using gaussian_forward_exponents (k : ℝ) z x
  have hb : f (z + x) = c * Complex.exp (magneticExponent (k : ℝ) z x) * f z :=
    (latticeBoundary_iff_forward G.M k G.omega1 G.omega2
      theta.theta1 theta.theta2 f).mp hf p z
  change holomorphicPart k f (z + x) =
    c * Complex.exp ((k : ℂ) * (z * conj x + x * conj x / 2)) *
      holomorphicPart k f z
  apply mul_left_cancel₀ (gaussianFactor_ne_zero (k : ℝ) (z + x))
  rw [gaussianFactor_holomorphicPart, hb,
    ← gaussianFactor_holomorphicPart k f z]
  unfold gaussianFactor
  simp only [Complex.ofReal_natCast]
  calc
    c * Complex.exp (magneticExponent (k : ℝ) z x) *
        (Complex.exp (-(k : ℂ) * (z * conj z) / 2) * holomorphicPart k f z) =
      c * Complex.exp (magneticExponent (k : ℝ) z x +
        -(k : ℂ) * (z * conj z) / 2) * holomorphicPart k f z := by
          rw [Complex.exp_add]
          ring
    _ = c * Complex.exp (-(k : ℂ) * ((z + x) * conj (z + x)) / 2 +
        (k : ℂ) * (z * conj x + x * conj x / 2)) * holomorphicPart k f z := by
          rw [hg]
    _ = Complex.exp (-(k : ℂ) * ((z + x) * conj (z + x)) / 2) *
        (c * Complex.exp ((k : ℂ) * (z * conj x + x * conj x / 2)) *
          holomorphicPart k f z) := by
          rw [Complex.exp_add]
          ring

theorem latticeChi_one_inverse (G : Geometry) (theta : Twist) (k : ℕ) :
    (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k)⁻¹ =
      Complex.exp (-(k : ℂ) * (theta.theta1 : ℂ) * Complex.I) := by
  rw [latticeChi, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  congr 1
  simp only [twistExponent, Complex.ofReal_add, Complex.ofReal_mul,
    Int.cast_one, Int.cast_zero, one_mul, zero_mul, mul_zero, add_zero,
    Complex.ofReal_natCast]
  ring

theorem latticeChi_two_inverse (G : Geometry) (theta : Twist) (k : ℕ) :
    (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k)⁻¹ =
      Complex.exp (-(k : ℂ) * (theta.theta2 : ℂ) * Complex.I) := by
  rw [latticeChi, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  congr 1
  simp only [twistExponent, Complex.ofReal_add, Complex.ofReal_mul,
    Int.cast_one, Int.cast_zero, one_mul, zero_mul, mul_zero, zero_add,
    add_zero, Complex.ofReal_natCast]
  ring

/-- The explicit map on actual universal-cover functions. -/
def gaugeSection (G : Geometry) (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun w => Complex.exp (-thetaAlpha G k * w ^ 2) *
    holomorphicPart k f (G.omega1 * w)

theorem gaugeSection_differentiable (G : Geometry) (k : ℕ) (f : ℂ → ℂ)
    (hf : IsGaussianHolomorphic (k : ℝ) f) :
    Differentiable ℂ (gaugeSection G k f) := by
  exact (((differentiable_id.pow 2).const_mul (-thetaAlpha G k)).cexp).mul
    ((holomorphicPart_differentiable k f hf).comp
      (differentiable_id.const_mul G.omega1))

theorem gaugeSection_add_one (G : Geometry) (theta : Twist) (k : ℕ)
    (f : ℂ → ℂ)
    (hf : HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 f)
    (w : ℂ) :
    gaugeSection G k f (w + 1) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * thetaSigma theta k) *
        gaugeSection G k f w := by
  have hb := holomorphicPart_forward G theta k f hf (1, 0) (G.omega1 * w)
  simp only [latticePeriod, Int.cast_one, Int.cast_zero, one_mul, zero_mul,
    add_zero, latticeChi_one_inverse] at hb
  have he : -thetaAlpha G k * (w + 1) ^ 2 +
      (-(k : ℂ) * (theta.theta1 : ℂ) * Complex.I +
        (k : ℂ) * (G.omega1 * w * conj G.omega1 +
          G.omega1 * conj G.omega1 / 2)) =
      2 * (Real.pi : ℂ) * Complex.I * thetaSigma theta k +
        (-thetaAlpha G k * w ^ 2) := by
    rw [thetaSigma_exponent]
    unfold thetaAlpha
    ring
  unfold gaugeSection
  rw [mul_add, mul_one, hb]
  calc
    _ = Complex.exp (-thetaAlpha G k * (w + 1) ^ 2 +
        (-(k : ℂ) * (theta.theta1 : ℂ) * Complex.I +
          (k : ℂ) * (G.omega1 * w * conj G.omega1 +
            G.omega1 * conj G.omega1 / 2))) *
        holomorphicPart k f (G.omega1 * w) := by
      rw [Complex.exp_add, Complex.exp_add]
      ring
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * thetaSigma theta k +
        (-thetaAlpha G k * w ^ 2)) * holomorphicPart k f (G.omega1 * w) := by
      rw [he]
    _ = _ := by rw [Complex.exp_add]; ring

theorem gauge_tau_exponents (G : Geometry) (theta : Twist) (k : ℕ) (w : ℂ) :
    -thetaAlpha G k * (w + thetaTau G) ^ 2 +
      (-(k : ℂ) * (theta.theta2 : ℂ) * Complex.I +
        (k : ℂ) * (G.omega1 * w * conj G.omega2 +
          G.omega2 * conj G.omega2 / 2)) =
      Complex.I * thetaPsi theta k -
        (Real.pi : ℂ) * Complex.I * ((k * G.M : ℕ) : ℂ) *
          (2 * w + thetaTau G) + (-thetaAlpha G k * w ^ 2) := by
  calc
    _ = -(k : ℂ) * (theta.theta2 : ℂ) * Complex.I - thetaAlpha G k * w ^ 2 +
        (k : ℂ) * (G.omega1 * conj G.omega2 - G.omega2 * conj G.omega1) *
          (w + thetaTau G / 2) := by
            unfold thetaAlpha
            rw [← omega1_mul_thetaTau G]
            simp only [map_mul]
            ring
    _ = _ := by
      rw [geometry_cross_eq_flux]
      simp only [Nat.cast_mul, thetaPsi]
      ring

theorem gaugeSection_add_tau (G : Geometry) (theta : Twist) (k : ℕ)
    (f : ℂ → ℂ)
    (hf : HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 f)
    (w : ℂ) :
    gaugeSection G k f (w + thetaTau G) =
      Complex.exp (Complex.I * thetaPsi theta k -
        (Real.pi : ℂ) * Complex.I * ((k * G.M : ℕ) : ℂ) *
          (2 * w + thetaTau G)) * gaugeSection G k f w := by
  have hb := holomorphicPart_forward G theta k f hf (0, 1) (G.omega1 * w)
  simp only [latticePeriod, Int.cast_one, Int.cast_zero, one_mul, zero_mul,
    zero_add, latticeChi_two_inverse] at hb
  unfold gaugeSection
  rw [mul_add, omega1_mul_thetaTau, hb]
  calc
    _ = Complex.exp (-thetaAlpha G k * (w + thetaTau G) ^ 2 +
        (-(k : ℂ) * (theta.theta2 : ℂ) * Complex.I +
          (k : ℂ) * (G.omega1 * w * conj G.omega2 +
            G.omega2 * conj G.omega2 / 2))) *
        holomorphicPart k f (G.omega1 * w) := by
      rw [Complex.exp_add, Complex.exp_add]
      ring
    _ = Complex.exp (Complex.I * thetaPsi theta k -
        (Real.pi : ℂ) * Complex.I * ((k * G.M : ℕ) : ℂ) *
          (2 * w + thetaTau G) + (-thetaAlpha G k * w ^ 2)) *
        holomorphicPart k f (G.omega1 * w) := by
      rw [gauge_tau_exponents]
    _ = _ := by rw [Complex.exp_add]; ring

/-- Linear injection into the analytically classified actual section space. -/
def gaugeMap (G : Geometry) (theta : Twist) (k : ℕ) :
    rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 →ₗ[ℂ]
      ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
        (thetaSigma theta k) (thetaPsi theta k) where
  toFun f := ⟨gaugeSection G k f,
    gaugeSection_differentiable G k f f.property.1,
    gaugeSection_add_one G theta k f f.property.2,
    gaugeSection_add_tau G theta k f f.property.2⟩
  map_add' f g := by
    apply Subtype.ext
    funext w
    change Complex.exp (-thetaAlpha G k * w ^ 2) *
        ((f.val (G.omega1 * w) + g.val (G.omega1 * w)) /
          gaussianFactor (k : ℝ) (G.omega1 * w)) =
      Complex.exp (-thetaAlpha G k * w ^ 2) *
          (f.val (G.omega1 * w) / gaussianFactor (k : ℝ) (G.omega1 * w)) +
        Complex.exp (-thetaAlpha G k * w ^ 2) *
          (g.val (G.omega1 * w) / gaussianFactor (k : ℝ) (G.omega1 * w))
    rw [add_div, mul_add]
  map_smul' c f := by
    apply Subtype.ext
    funext w
    change Complex.exp (-thetaAlpha G k * w ^ 2) *
        ((c * f.val (G.omega1 * w)) / gaussianFactor (k : ℝ) (G.omega1 * w)) =
      c * (Complex.exp (-thetaAlpha G k * w ^ 2) *
        (f.val (G.omega1 * w) / gaussianFactor (k : ℝ) (G.omega1 * w)))
    ring

theorem gaugeMap_injective (G : Geometry) (theta : Twist) (k : ℕ) :
    Function.Injective (gaugeMap G theta k) := by
  intro f g h
  apply Subtype.ext
  funext z
  have he := congrFun (congrArg Subtype.val h) (z / G.omega1)
  change Complex.exp (-thetaAlpha G k * (z / G.omega1) ^ 2) *
      holomorphicPart k f (G.omega1 * (z / G.omega1)) =
    Complex.exp (-thetaAlpha G k * (z / G.omega1) ^ 2) *
      holomorphicPart k g (G.omega1 * (z / G.omega1)) at he
  have hz : G.omega1 * (z / G.omega1) = z := by
    field_simp [geometry_omega1_ne_zero G]
    <;> ring
  rw [hz] at he
  have hp := mul_left_cancel₀ (Complex.exp_ne_zero _) he
  calc
    f.val z = gaussianFactor (k : ℝ) z * holomorphicPart k f z :=
      (gaussianFactor_holomorphicPart k f z).symm
    _ = gaussianFactor (k : ℝ) z * holomorphicPart k g z := by rw [hp]
    _ = g.val z := gaussianFactor_holomorphicPart k g z

/-- Finite dimension of the actual physical section submodule, derived from
the concrete gauge injection and the accepted analytic exhaustion theorem. -/
theorem rawLLLSubmodule_finiteDimensional (G : Geometry) (theta : Twist) (k : ℕ)
    (hk : 0 < k) :
    FiniteDimensional ℂ
      (rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2) := by
  letI : NeZero (k * G.M) := ⟨Nat.ne_of_gt (Nat.mul_pos hk G.flux_pos)⟩
  letI : FiniteDimensional ℂ
      (ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
        (thetaSigma theta k) (thetaPsi theta k)) :=
    ThetaFourier.entireSectionSpace_finiteDimensional (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k) (thetaTau_im_pos G)
  exact FiniteDimensional.of_injective (gaugeMap G theta k)
    (gaugeMap_injective G theta k)

/-- Only an upper bound is claimed: reverse all-period construction is not
part of this module. -/
theorem rawLLLSubmodule_finrank_le (G : Geometry) (theta : Twist) (k : ℕ)
    (hk : 0 < k) :
    Module.finrank ℂ
      (rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2) ≤ k * G.M := by
  letI : NeZero (k * G.M) := ⟨Nat.ne_of_gt (Nat.mul_pos hk G.flux_pos)⟩
  letI : FiniteDimensional ℂ
      (ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
        (thetaSigma theta k) (thetaPsi theta k)) :=
    ThetaFourier.entireSectionSpace_finiteDimensional (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k) (thetaTau_im_pos G)
  calc
    _ ≤ Module.finrank ℂ
        (ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
          (thetaSigma theta k) (thetaPsi theta k)) :=
      LinearMap.finrank_le_finrank_of_injective (gaugeMap_injective G theta k)
    _ = k * G.M := ThetaFourier.entireSection_finrank (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k) (thetaTau_im_pos G)

#print axioms geometry_omega1_ne_zero
#print axioms thetaTau_im_pos
#print axioms geometry_cross_eq_flux
#print axioms holomorphicPart_differentiable
#print axioms holomorphicPart_forward
#print axioms gaugeSection_add_one
#print axioms gaugeSection_add_tau
#print axioms gaugeMap_injective
#print axioms rawLLLSubmodule_finiteDimensional
#print axioms rawLLLSubmodule_finrank_le

end TorusLean.Shared
