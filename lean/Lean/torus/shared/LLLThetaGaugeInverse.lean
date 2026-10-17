import torus.shared.CellHilbert
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Explicit inverse theta gauge and exact physical LLL dimension

An actual entire theta section is taken back to a universal-cover physical
section by undoing the quadratic gauge and replacing the physical Gaussian.
Its two generator boundary laws are first proved with inverse chi in the
forward direction. The magnetic cocycle and the actual chi semicharacter then
extend the eigenboundary to every integer lattice pair, including negative
indices. Thus the target is the existing all-period raw physical section
module, not a section class defined using only two unextended generators.

The inverse is complex linear and inverse to the previously accepted gaugeMap.
Analytic Fourier classification consequently proves physical finrank=k*M.
No Hamiltonian, contact kernel, gap, periodized reproducing-kernel identity,
or Jastrow/COM descent conclusion is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared

open TorusLean.Geometry
open scoped ComplexConjugate

theorem inverse_latticePeriod_neg (G : Geometry) (p : ℤ × ℤ) :
    latticePeriod G.omega1 G.omega2 (-p) = -latticePeriod G.omega1 G.omega2 p := by
  simp only [latticePeriod, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

theorem inverse_latticeChi_zero (G : Geometry) (theta : Twist) :
    latticeChi G.M theta.theta1 theta.theta2 (0 : ℤ × ℤ) = 1 := by
  simp [latticeChi, twistExponent]

/-- The actual chi semicharacter at physical integer charge, with the actual
charge-k magnetic cocycle. The shared area identity is used explicitly. -/
theorem inverse_chargeChi_semicharacter (G : Geometry) (theta : Twist) (k : ℕ)
    (p q : ℤ × ℤ) :
    latticeChi G.M theta.theta1 theta.theta2 p ^ k *
        latticeChi G.M theta.theta1 theta.theta2 q ^ k =
      magneticCocycle (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
        (latticePeriod G.omega1 G.omega2 q) *
          latticeChi G.M theta.theta1 theta.theta2 (p + q) ^ k := by
  calc
    _ = (latticeChi G.M theta.theta1 theta.theta2 p *
        latticeChi G.M theta.theta1 theta.theta2 q) ^ k := (mul_pow _ _ k).symm
    _ = (magneticCocycle 1 (latticePeriod G.omega1 G.omega2 p)
        (latticePeriod G.omega1 G.omega2 q) *
          latticeChi G.M theta.theta1 theta.theta2 (p + q)) ^ k := by
      rw [latticeChi_semicharacter G.M G.omega1 G.omega2 G.area]
    _ = magneticCocycle 1 (latticePeriod G.omega1 G.omega2 p)
        (latticePeriod G.omega1 G.omega2 q) ^ k *
          latticeChi G.M theta.theta1 theta.theta2 (p + q) ^ k := mul_pow _ _ k
    _ = _ := by rw [magneticCocycle_nat_charge]

theorem inverse_boundary_add (G : Geometry) (theta : Twist) (k : ℕ)
    (f : ℂ → ℂ) (p q : ℤ × ℤ)
    (hp : HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
      (latticeChi G.M theta.theta1 theta.theta2 p ^ k) f)
    (hq : HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 q)
      (latticeChi G.M theta.theta1 theta.theta2 q ^ k) f) :
    HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 (p + q))
      (latticeChi G.M theta.theta1 theta.theta2 (p + q) ^ k) f := by
  unfold HasMagneticEigencharacter at hp hq ⊢
  rw [latticePeriod_add]
  funext z
  have hcomp := magneticTranslate_comp (k : ℝ)
    (latticePeriod G.omega1 G.omega2 p) (latticePeriod G.omega1 G.omega2 q) f
  rw [hq, magneticTranslate_const_mul, hp] at hcomp
  have hz := congrFun hcomp z
  change latticeChi G.M theta.theta1 theta.theta2 q ^ k *
      (latticeChi G.M theta.theta1 theta.theta2 p ^ k * f z) =
    magneticCocycle (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
      (latticePeriod G.omega1 G.omega2 q) *
        magneticTranslate (k : ℝ) (latticePeriod G.omega1 G.omega2 p +
          latticePeriod G.omega1 G.omega2 q) f z at hz
  apply mul_left_cancel₀ (show magneticCocycle (k : ℝ)
      (latticePeriod G.omega1 G.omega2 p) (latticePeriod G.omega1 G.omega2 q) ≠ 0 from
    Complex.exp_ne_zero _)
  calc
    _ = latticeChi G.M theta.theta1 theta.theta2 q ^ k *
        (latticeChi G.M theta.theta1 theta.theta2 p ^ k * f z) := hz.symm
    _ = (latticeChi G.M theta.theta1 theta.theta2 p ^ k *
        latticeChi G.M theta.theta1 theta.theta2 q ^ k) * f z := by ring
    _ = (magneticCocycle (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
        (latticePeriod G.omega1 G.omega2 q) *
          latticeChi G.M theta.theta1 theta.theta2 (p + q) ^ k) * f z := by
      rw [inverse_chargeChi_semicharacter G theta k p q]
    _ = _ := by ring

theorem inverse_boundary_neg (G : Geometry) (theta : Twist) (k : ℕ)
    (f : ℂ → ℂ) (p : ℤ × ℤ)
    (hp : HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
      (latticeChi G.M theta.theta1 theta.theta2 p ^ k) f) :
    HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 (-p))
      (latticeChi G.M theta.theta1 theta.theta2 (-p) ^ k) f := by
  have hchi : latticeChi G.M theta.theta1 theta.theta2 (-p) ^ k *
      latticeChi G.M theta.theta1 theta.theta2 p ^ k = 1 := by
    rw [inverse_chargeChi_semicharacter, inverse_latticePeriod_neg]
    have hc : magneticCocycle (k : ℝ) (-latticePeriod G.omega1 G.omega2 p)
        (latticePeriod G.omega1 G.omega2 p) = 1 := by
      simpa only [neg_neg] using magneticCocycle_neg_self (k : ℝ)
        (-latticePeriod G.omega1 G.omega2 p)
    rw [hc, neg_add_cancel, inverse_latticeChi_zero]
    simp
  unfold HasMagneticEigencharacter at hp ⊢
  have hi := magneticTranslate_inverse (k : ℝ) (-latticePeriod G.omega1 G.omega2 p) f
  simp only [neg_neg] at hi
  rw [hp, magneticTranslate_const_mul] at hi
  rw [inverse_latticePeriod_neg]
  funext z
  have hz := congrFun hi z
  change latticeChi G.M theta.theta1 theta.theta2 p ^ k *
      magneticTranslate (k : ℝ) (-latticePeriod G.omega1 G.omega2 p) f z = f z at hz
  calc
    _ = (latticeChi G.M theta.theta1 theta.theta2 (-p) ^ k *
        latticeChi G.M theta.theta1 theta.theta2 p ^ k) *
          magneticTranslate (k : ℝ) (-latticePeriod G.omega1 G.omega2 p) f z := by
      rw [hchi, one_mul]
    _ = latticeChi G.M theta.theta1 theta.theta2 (-p) ^ k *
        (latticeChi G.M theta.theta1 theta.theta2 p ^ k *
          magneticTranslate (k : ℝ) (-latticePeriod G.omega1 G.omega2 p) f z) := by ring
    _ = _ := by rw [hz]

/-- Actual integer lattice indices where the physical magnetic eigenboundary
holds. Its subgroup structure is proved from the magnetic/chi identities. -/
def inverseBoundaryPeriods (G : Geometry) (theta : Twist) (k : ℕ) (f : ℂ → ℂ) :
    AddSubgroup (ℤ × ℤ) where
  carrier := {p | HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 p)
    (latticeChi G.M theta.theta1 theta.theta2 p ^ k) f}
  zero_mem' := by
    change HasMagneticEigencharacter (k : ℝ)
      (latticePeriod G.omega1 G.omega2 (0 : ℤ × ℤ))
      (latticeChi G.M theta.theta1 theta.theta2 (0 : ℤ × ℤ) ^ k) f
    unfold HasMagneticEigencharacter
    funext z
    simp [latticePeriod, latticeChi, twistExponent, magneticTranslate, magneticExponent]
  add_mem' := by
    intro p q hp hq
    exact inverse_boundary_add G theta k f p q hp hq
  neg_mem' := by
    intro p hp
    exact inverse_boundary_neg G theta k f p hp

/-- The two generator laws imply the original law for every integer period.
In particular mixed indices retain the flux-parity part of chi. -/
theorem latticeBoundary_of_generators (G : Geometry) (theta : Twist) (k : ℕ)
    (f : ℂ → ℂ)
    (h1 : HasMagneticEigencharacter (k : ℝ) G.omega1
      (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k) f)
    (h2 : HasMagneticEigencharacter (k : ℝ) G.omega2
      (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k) f) :
    HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 f := by
  let S := inverseBoundaryPeriods G theta k f
  have h1S : (1, 0) ∈ S := by
    change HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 (1, 0))
      (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k) f
    simpa only [latticePeriod, Int.cast_one, Int.cast_zero, one_mul, zero_mul,
      add_zero] using h1
  have h2S : (0, 1) ∈ S := by
    change HasMagneticEigencharacter (k : ℝ) (latticePeriod G.omega1 G.omega2 (0, 1))
      (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k) f
    simpa only [latticePeriod, Int.cast_one, Int.cast_zero, one_mul, zero_mul,
      zero_add] using h2
  intro p
  have hp := S.add_mem (S.zsmul_mem h1S p.1) (S.zsmul_mem h2S p.2)
  have hdecomp : p.1 • ((1, 0) : ℤ × ℤ) + p.2 • ((0, 1) : ℤ × ℤ) = p := by
    ext <;> simp
  rw [hdecomp] at hp
  exact hp

/-- Explicit inverse holomorphic gauge on actual entire theta functions. -/
def inverseHolomorphicPart (G : Geometry) (k : ℕ) (H : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (thetaAlpha G k * (z / G.omega1) ^ 2) * H (z / G.omega1)

/-- Replace the physical Gaussian after undoing the entire quadratic gauge. -/
def inverseGaugeSection (G : Geometry) (k : ℕ) (H : ℂ → ℂ) : ℂ → ℂ :=
  fun z => gaussianFactor (k : ℝ) z * inverseHolomorphicPart G k H z

theorem inverseHolomorphicPart_differentiable (G : Geometry) (k : ℕ)
    (H : ℂ → ℂ) (hH : Differentiable ℂ H) :
    Differentiable ℂ (inverseHolomorphicPart G k H) := by
  have hs : Differentiable ℂ (fun z : ℂ => z / G.omega1) :=
    differentiable_id.div_const G.omega1
  exact ((hs.pow 2).const_mul (thetaAlpha G k)).cexp.mul (hH.comp hs)

theorem inverseGaugeSection_gaussianHolomorphic (G : Geometry) (k : ℕ)
    (H : ℂ → ℂ) (hH : Differentiable ℂ H) :
    IsGaussianHolomorphic (k : ℝ) (inverseGaugeSection G k H) :=
  ⟨inverseHolomorphicPart G k H, inverseHolomorphicPart_differentiable G k H hH,
    fun _ => rfl⟩

theorem inverseScale_mul (G : Geometry) (w : ℂ) : G.omega1 * w / G.omega1 = w := by
  field_simp [geometry_omega1_ne_zero G]
  <;> ring

theorem inverseScale_add_one (G : Geometry) (w : ℂ) :
    (G.omega1 * w + G.omega1) / G.omega1 = w + 1 := by
  rw [add_div, inverseScale_mul, div_self (geometry_omega1_ne_zero G)]

theorem inverseScale_add_tau (G : Geometry) (w : ℂ) :
    (G.omega1 * w + G.omega2) / G.omega1 = w + thetaTau G := by
  rw [add_div, inverseScale_mul]
  rfl

theorem holomorphicPart_inverseGaugeSection (G : Geometry) (k : ℕ) (H : ℂ → ℂ) :
    holomorphicPart k (inverseGaugeSection G k H) = inverseHolomorphicPart G k H :=
  holomorphicPart_eq_factor k _ _ (fun _ => rfl)

theorem gaugeSection_inverseGaugeSection (G : Geometry) (k : ℕ) (H : ℂ → ℂ) :
    gaugeSection G k (inverseGaugeSection G k H) = H := by
  funext w
  unfold gaugeSection
  rw [holomorphicPart_inverseGaugeSection]
  simp only [inverseHolomorphicPart, inverseScale_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  have he : -thetaAlpha G k * w ^ 2 + thetaAlpha G k * w ^ 2 = 0 := by ring
  rw [he, Complex.exp_zero, one_mul]

theorem inverseHolomorphicPart_add_one (G : Geometry) (theta : Twist) (k : ℕ)
    (H : ℂ → ℂ)
    (hH : ∀ w, H (w + 1) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * thetaSigma theta k) * H w)
    (w : ℂ) :
    inverseHolomorphicPart G k H (G.omega1 * w + G.omega1) =
      (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k)⁻¹ *
        Complex.exp ((k : ℂ) * (G.omega1 * w * conj G.omega1 +
          G.omega1 * conj G.omega1 / 2)) *
            inverseHolomorphicPart G k H (G.omega1 * w) := by
  simp only [inverseHolomorphicPart, inverseScale_add_one, inverseScale_mul]
  rw [hH, thetaSigma_exponent, latticeChi_one_inverse]
  have he : thetaAlpha G k * (w + 1) ^ 2 +
      (-(k : ℂ) * (theta.theta1 : ℂ) * Complex.I) =
    -(k : ℂ) * (theta.theta1 : ℂ) * Complex.I +
      (k : ℂ) * (G.omega1 * w * conj G.omega1 +
        G.omega1 * conj G.omega1 / 2) + thetaAlpha G k * w ^ 2 := by
    unfold thetaAlpha
    ring
  calc
    _ = Complex.exp (thetaAlpha G k * (w + 1) ^ 2 +
        (-(k : ℂ) * (theta.theta1 : ℂ) * Complex.I)) * H w := by
      rw [Complex.exp_add]
      ring
    _ = Complex.exp (-(k : ℂ) * (theta.theta1 : ℂ) * Complex.I +
        (k : ℂ) * (G.omega1 * w * conj G.omega1 +
          G.omega1 * conj G.omega1 / 2) + thetaAlpha G k * w ^ 2) * H w := by rw [he]
    _ = _ := by rw [Complex.exp_add, Complex.exp_add]; ring

theorem inverse_tau_exponents (G : Geometry) (theta : Twist) (k : ℕ) (w : ℂ) :
    thetaAlpha G k * (w + thetaTau G) ^ 2 +
      (Complex.I * thetaPsi theta k - (Real.pi : ℂ) * Complex.I *
        ((k * G.M : ℕ) : ℂ) * (2 * w + thetaTau G)) =
    -(k : ℂ) * (theta.theta2 : ℂ) * Complex.I +
      (k : ℂ) * (G.omega1 * w * conj G.omega2 +
        G.omega2 * conj G.omega2 / 2) + thetaAlpha G k * w ^ 2 := by
  calc
    _ = (Complex.I * thetaPsi theta k - (Real.pi : ℂ) * Complex.I *
        ((k * G.M : ℕ) : ℂ) * (2 * w + thetaTau G) +
          (-thetaAlpha G k * w ^ 2)) +
        thetaAlpha G k * (w + thetaTau G) ^ 2 + thetaAlpha G k * w ^ 2 := by ring
    _ = (-thetaAlpha G k * (w + thetaTau G) ^ 2 +
        (-(k : ℂ) * (theta.theta2 : ℂ) * Complex.I +
          (k : ℂ) * (G.omega1 * w * conj G.omega2 +
            G.omega2 * conj G.omega2 / 2))) +
        thetaAlpha G k * (w + thetaTau G) ^ 2 + thetaAlpha G k * w ^ 2 := by
      rw [← gauge_tau_exponents]
    _ = _ := by ring

theorem inverseHolomorphicPart_add_tau (G : Geometry) (theta : Twist) (k : ℕ)
    (H : ℂ → ℂ)
    (hH : ∀ w, H (w + thetaTau G) =
      Complex.exp (Complex.I * thetaPsi theta k - (Real.pi : ℂ) * Complex.I *
        ((k * G.M : ℕ) : ℂ) * (2 * w + thetaTau G)) * H w) (w : ℂ) :
    inverseHolomorphicPart G k H (G.omega1 * w + G.omega2) =
      (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k)⁻¹ *
        Complex.exp ((k : ℂ) * (G.omega1 * w * conj G.omega2 +
          G.omega2 * conj G.omega2 / 2)) *
            inverseHolomorphicPart G k H (G.omega1 * w) := by
  simp only [inverseHolomorphicPart, inverseScale_add_tau, inverseScale_mul]
  rw [hH, latticeChi_two_inverse]
  calc
    _ = Complex.exp (thetaAlpha G k * (w + thetaTau G) ^ 2 +
        (Complex.I * thetaPsi theta k - (Real.pi : ℂ) * Complex.I *
          ((k * G.M : ℕ) : ℂ) * (2 * w + thetaTau G))) * H w := by
      rw [Complex.exp_add]
      ring
    _ = Complex.exp (-(k : ℂ) * (theta.theta2 : ℂ) * Complex.I +
        (k : ℂ) * (G.omega1 * w * conj G.omega2 +
          G.omega2 * conj G.omega2 / 2) + thetaAlpha G k * w ^ 2) * H w := by
      rw [inverse_tau_exponents]
    _ = _ := by rw [Complex.exp_add, Complex.exp_add]; ring

/-- Exact Gaussian identity converting the holomorphic multiplier back to
the magnetic forward multiplier. -/
theorem inverse_gaussian_forward_multiplier (k : ℕ) (z x : ℂ) :
    gaussianFactor (k : ℝ) (z + x) *
        Complex.exp ((k : ℂ) * (z * conj x + x * conj x / 2)) =
      Complex.exp (magneticExponent (k : ℝ) z x) * gaussianFactor (k : ℝ) z := by
  unfold gaussianFactor
  simp only [Complex.ofReal_natCast]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simpa only [Complex.ofReal_natCast] using (gaussian_forward_exponents (k : ℝ) z x).symm

theorem inverseGaugeSection_one_boundary (G : Geometry) (theta : Twist) (k : ℕ)
    (H : ℂ → ℂ)
    (hH : ∀ w, H (w + 1) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * thetaSigma theta k) * H w) :
    HasMagneticEigencharacter (k : ℝ) G.omega1
      (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k) (inverseGaugeSection G k H) := by
  apply (magneticEigencharacter_iff_forward (k : ℝ) G.omega1 _
    (pow_ne_zero k (latticeChi_ne_zero G.M theta.theta1 theta.theta2 (1, 0))) _).mpr
  intro z
  have hz : G.omega1 * (z / G.omega1) = z := by
    field_simp [geometry_omega1_ne_zero G]
    <;> ring
  have hF := inverseHolomorphicPart_add_one G theta k H hH (z / G.omega1)
  rw [hz] at hF
  change gaussianFactor (k : ℝ) (z + G.omega1) *
      inverseHolomorphicPart G k H (z + G.omega1) =
    (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k)⁻¹ *
      Complex.exp (magneticExponent (k : ℝ) z G.omega1) *
        (gaussianFactor (k : ℝ) z * inverseHolomorphicPart G k H z)
  rw [hF]
  calc
    _ = (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k)⁻¹ *
        (gaussianFactor (k : ℝ) (z + G.omega1) *
          Complex.exp ((k : ℂ) * (z * conj G.omega1 +
            G.omega1 * conj G.omega1 / 2))) * inverseHolomorphicPart G k H z := by ring
    _ = (latticeChi G.M theta.theta1 theta.theta2 (1, 0) ^ k)⁻¹ *
        (Complex.exp (magneticExponent (k : ℝ) z G.omega1) * gaussianFactor (k : ℝ) z) *
          inverseHolomorphicPart G k H z := by rw [inverse_gaussian_forward_multiplier]
    _ = _ := by ring

theorem inverseGaugeSection_two_boundary (G : Geometry) (theta : Twist) (k : ℕ)
    (H : ℂ → ℂ)
    (hH : ∀ w, H (w + thetaTau G) =
      Complex.exp (Complex.I * thetaPsi theta k - (Real.pi : ℂ) * Complex.I *
        ((k * G.M : ℕ) : ℂ) * (2 * w + thetaTau G)) * H w) :
    HasMagneticEigencharacter (k : ℝ) G.omega2
      (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k) (inverseGaugeSection G k H) := by
  apply (magneticEigencharacter_iff_forward (k : ℝ) G.omega2 _
    (pow_ne_zero k (latticeChi_ne_zero G.M theta.theta1 theta.theta2 (0, 1))) _).mpr
  intro z
  have hz : G.omega1 * (z / G.omega1) = z := by
    field_simp [geometry_omega1_ne_zero G]
    <;> ring
  have hF := inverseHolomorphicPart_add_tau G theta k H hH (z / G.omega1)
  rw [hz] at hF
  change gaussianFactor (k : ℝ) (z + G.omega2) *
      inverseHolomorphicPart G k H (z + G.omega2) =
    (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k)⁻¹ *
      Complex.exp (magneticExponent (k : ℝ) z G.omega2) *
        (gaussianFactor (k : ℝ) z * inverseHolomorphicPart G k H z)
  rw [hF]
  calc
    _ = (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k)⁻¹ *
        (gaussianFactor (k : ℝ) (z + G.omega2) *
          Complex.exp ((k : ℂ) * (z * conj G.omega2 +
            G.omega2 * conj G.omega2 / 2))) * inverseHolomorphicPart G k H z := by ring
    _ = (latticeChi G.M theta.theta1 theta.theta2 (0, 1) ^ k)⁻¹ *
        (Complex.exp (magneticExponent (k : ℝ) z G.omega2) * gaussianFactor (k : ℝ) z) *
          inverseHolomorphicPart G k H z := by rw [inverse_gaussian_forward_multiplier]
    _ = _ := by ring

theorem inverseGaugeSection_latticeBoundary (G : Geometry) (theta : Twist) (k : ℕ)
    (H : ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k)) :
    HasLatticeBoundary G.M k G.omega1 G.omega2 theta.theta1 theta.theta2
      (inverseGaugeSection G k H.val) :=
  latticeBoundary_of_generators G theta k _
    (inverseGaugeSection_one_boundary G theta k H.val H.property.2.1)
    (inverseGaugeSection_two_boundary G theta k H.val H.property.2.2)

/-- Explicit complex-linear inverse, into the existing all-period physical
section submodule. Every differential and boundary condition is proved. -/
def inverseGaugeMap (G : Geometry) (theta : Twist) (k : ℕ) :
    ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k) →ₗ[ℂ]
        rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 where
  toFun H := ⟨inverseGaugeSection G k H.val,
    inverseGaugeSection_gaussianHolomorphic G k H.val H.property.1,
    inverseGaugeSection_latticeBoundary G theta k H⟩
  map_add' H J := by
    apply Subtype.ext
    funext z
    change gaussianFactor (k : ℝ) z *
        (Complex.exp (thetaAlpha G k * (z / G.omega1) ^ 2) *
          (H.val (z / G.omega1) + J.val (z / G.omega1))) =
      gaussianFactor (k : ℝ) z *
          (Complex.exp (thetaAlpha G k * (z / G.omega1) ^ 2) * H.val (z / G.omega1)) +
        gaussianFactor (k : ℝ) z *
          (Complex.exp (thetaAlpha G k * (z / G.omega1) ^ 2) * J.val (z / G.omega1))
    ring
  map_smul' c H := by
    apply Subtype.ext
    funext z
    change gaussianFactor (k : ℝ) z *
        (Complex.exp (thetaAlpha G k * (z / G.omega1) ^ 2) *
          (c * H.val (z / G.omega1))) =
      c * (gaussianFactor (k : ℝ) z *
        (Complex.exp (thetaAlpha G k * (z / G.omega1) ^ 2) * H.val (z / G.omega1)))
    ring

theorem gaugeMap_inverseGaugeMap (G : Geometry) (theta : Twist) (k : ℕ)
    (H : ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k)) :
    gaugeMap G theta k (inverseGaugeMap G theta k H) = H := by
  apply Subtype.ext
  exact gaugeSection_inverseGaugeSection G k H.val

theorem gaugeMap_surjective (G : Geometry) (theta : Twist) (k : ℕ) :
    Function.Surjective (gaugeMap G theta k) := by
  intro H
  exact ⟨inverseGaugeMap G theta k H, gaugeMap_inverseGaugeMap G theta k H⟩

theorem inverseGaugeMap_gaugeMap (G : Geometry) (theta : Twist) (k : ℕ)
    (f : rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2) :
    inverseGaugeMap G theta k (gaugeMap G theta k f) = f := by
  apply gaugeMap_injective G theta k
  exact gaugeMap_inverseGaugeMap G theta k (gaugeMap G theta k f)

/-- The actual physical raw LLL and the independently classified actual
theta section space, with the displayed explicit inverse gauge. -/
def physicalThetaGaugeEquiv (G : Geometry) (theta : Twist) (k : ℕ) :
    rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2 ≃ₗ[ℂ]
      ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
        (thetaSigma theta k) (thetaPsi theta k) :=
  LinearEquiv.ofLinearMap (gaugeMap G theta k) (inverseGaugeMap G theta k)
    (by apply LinearMap.ext; intro H; exact gaugeMap_inverseGaugeMap G theta k H)
    (by apply LinearMap.ext; intro f; exact inverseGaugeMap_gaugeMap G theta k f)

theorem physicalThetaGaugeEquiv_apply (G : Geometry) (theta : Twist) (k : ℕ)
    (f : rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2) :
    physicalThetaGaugeEquiv G theta k f = gaugeMap G theta k f := rfl

theorem physicalThetaGaugeEquiv_symm_apply (G : Geometry) (theta : Twist) (k : ℕ)
    (H : ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k)) :
    (physicalThetaGaugeEquiv G theta k).symm H = inverseGaugeMap G theta k H := rfl

/-- Exact dimension of the actual all-period physical section submodule.
This consumes analytic Fourier classification after proving gauge surjectivity. -/
theorem rawLLLSubmodule_finrank_eq (G : Geometry) (theta : Twist) (k : ℕ)
    (hk : 0 < k) :
    Module.finrank ℂ
      (rawLLLSubmodule G.M k G.omega1 G.omega2 theta.theta1 theta.theta2) = k * G.M := by
  letI : NeZero (k * G.M) := ⟨Nat.ne_of_gt (Nat.mul_pos hk G.flux_pos)⟩
  calc
    _ = Module.finrank ℂ
        (ThetaFourier.entireSectionSpace (k * G.M) (thetaTau G)
          (thetaSigma theta k) (thetaPsi theta k)) :=
      (physicalThetaGaugeEquiv G theta k).finrank_eq
    _ = k * G.M := ThetaFourier.entireSection_finrank (k * G.M) (thetaTau G)
      (thetaSigma theta k) (thetaPsi theta k) (thetaTau_im_pos G)

/-- The same exact dimension for the physical cell Hilbert carrier. -/
theorem lll_finrank_eq (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    Module.finrank ℂ (LLL G theta k) = k * G.M :=
  (lllRawEquiv G theta k).finrank_eq.trans
    (rawLLLSubmodule_finrank_eq G theta k (NeZero.pos k))

theorem lll_finrank_pos (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    0 < Module.finrank ℂ (LLL G theta k) := by
  rw [lll_finrank_eq]
  exact Nat.mul_pos (NeZero.pos k) G.flux_pos

#print axioms inverse_chargeChi_semicharacter
#print axioms inverse_boundary_add
#print axioms inverse_boundary_neg
#print axioms inverseBoundaryPeriods
#print axioms latticeBoundary_of_generators
#print axioms inverseHolomorphicPart_differentiable
#print axioms inverseGaugeSection_gaussianHolomorphic
#print axioms gaugeSection_inverseGaugeSection
#print axioms inverseHolomorphicPart_add_one
#print axioms inverse_tau_exponents
#print axioms inverseHolomorphicPart_add_tau
#print axioms inverse_gaussian_forward_multiplier
#print axioms inverseGaugeSection_one_boundary
#print axioms inverseGaugeSection_two_boundary
#print axioms inverseGaugeSection_latticeBoundary
#print axioms inverseGaugeMap
#print axioms gaugeMap_inverseGaugeMap
#print axioms gaugeMap_surjective
#print axioms inverseGaugeMap_gaugeMap
#print axioms physicalThetaGaugeEquiv
#print axioms physicalThetaGaugeEquiv_symm_apply
#print axioms rawLLLSubmodule_finrank_eq
#print axioms lll_finrank_eq
#print axioms lll_finrank_pos

end TorusLean.Shared
