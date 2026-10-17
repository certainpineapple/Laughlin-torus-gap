import torus.shared.GroundJetReproducing
import torus.shared.CellHilbert
import torus.geometry.LatticeSummability
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic.Linarith

/-!
# Original charge-one periodized plane jets belong to the actual RawLLL

Every fixed canonical jet degree has a derived Gaussian-polynomial
majorant. Its original `sqrt(j!)` normalization, inverse semicharacter,
physical variable, centre, and both magnetic translations are retained.
The actual legal lattice supplies inverse-fourth-power summability, from
which the slower Gaussian majorant is derived. The exact stripped image
series converges uniformly on every finite closed ball and its sum is
entire. Combining that analytic condition with the original all-period
boundary law proves original charge-one RawLLL membership for every j.

The local majorant depends on j, R, and the finite ball. It is not a
uniform high-jet, shape, or physical-norm budget. No all-j reproducing or
Gram formula, derivative-contact identity, or fermionic Hamiltonian claim
is made here.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared.PlaneJetMembership

open Set Filter MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Shared.GroundJetReproducing
open scoped ComplexConjugate Topology

private theorem legal_area (G : Geometry) :
    latticeArea G.omega1 G.omega2 = Real.pi * (G.M : ℝ) := G.area

/-- The slower Gaussian needed after absorbing the actual polynomial
factor is still dominated by the accepted lattice inverse-fourth power. -/
theorem exp_neg_sq_div_eight_le_inv_pow (x : ℝ) (hx : 0 < x) :
    Real.exp (-x ^ 2 / 8) ≤ 128 * x⁻¹ ^ 4 := by
  have hp := Real.pow_div_factorial_le_exp (x := x ^ 2 / 8) (by positivity) 2
  have hp' : x ^ 4 ≤ 128 * Real.exp (x ^ 2 / 8) := by
    norm_num at hp
    nlinarith [hp]
  have hn : x ≠ 0 := ne_of_gt hx
  apply (mul_le_mul_iff_left₀ (pow_pos hx 4)).mp
  calc
    Real.exp (-x ^ 2 / 8) * x ^ 4 = x ^ 4 / Real.exp (x ^ 2 / 8) := by
      rw [show -x ^ 2 / 8 = -(x ^ 2 / 8) by ring, Real.exp_neg]
      ring
    _ ≤ 128 := (div_le_iff₀ (Real.exp_pos _)).mpr hp'
    _ = (128 * x⁻¹ ^ 4) * x ^ 4 := by
      simp only [mul_assoc, ← mul_pow, inv_mul_cancel₀ hn, one_pow, mul_one]

/-- Derived Gaussian summability for every legal original lattice. Only
the single zero image is omitted from the inverse-power comparison. -/
theorem lattice_planeJet_gaussian_summable (G : Geometry) :
    Summable (fun p : ℤ × ℤ =>
      Real.exp (-‖latticePeriod G.omega1 G.omega2 p‖ ^ 2 / 8)) := by
  have hs := (latticePeriod_summable_inv_pow G.M G.flux_pos G.omega1 G.omega2
    (legal_area G) 4 (by norm_num) 0).mul_left 128
  simp only [sub_zero] at hs
  apply hs.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ × ℤ)] with p hp
  have hperiod : latticePeriod G.omega1 G.omega2 p ≠ 0 := by
    intro h
    exact hp ((latticePeriod_eq_zero_iff G.M G.flux_pos G.omega1 G.omega2
      (legal_area G) p).mp h)
  simpa only [Real.norm_of_nonneg (Real.exp_nonneg _)] using
    exp_neg_sq_div_eight_le_inv_pow _ (norm_pos_iff.mpr hperiod)

/-- The original canonical normalization is positive; no zero-denominator
interpretation is used to obtain the jet majorant. -/
theorem planeJet_scale_pos (j : ℕ) : 0 < Real.sqrt (j.factorial : ℝ) :=
  Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos j)

/-- A concrete polynomial-growth constant for each actual canonical jet.
It is derived below, not supplied as a norm or convergence premise. -/
def planeJetPolynomialEnvelope (j : ℕ) : ℝ :=
  (1 + (4 : ℝ) ^ j * (j.factorial : ℝ)) / Real.sqrt (j.factorial : ℝ)

theorem planeJetPolynomialEnvelope_nonneg (j : ℕ) :
    0 ≤ planeJetPolynomialEnvelope j := by
  unfold planeJetPolynomialEnvelope
  positivity

/-- Every fixed natural monomial is absorbed by a quarter Gaussian.
The elementary bound is valid also at x = 0 and j = 0. -/
theorem natPower_le_gaussian_growth (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ j ≤ (1 + (4 : ℝ) ^ j * (j.factorial : ℝ)) * Real.exp (x ^ 2 / 4) := by
  have hfac : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hp : (x ^ 2 / 4) ^ j ≤ Real.exp (x ^ 2 / 4) * (j.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp
      (Real.pow_div_factorial_le_exp (x := x ^ 2 / 4) (by positivity) j)
  have hp' : (x ^ 2) ^ j ≤
      (4 : ℝ) ^ j * (j.factorial : ℝ) * Real.exp (x ^ 2 / 4) := by
    calc
      (x ^ 2) ^ j = (4 * (x ^ 2 / 4)) ^ j :=
        congrArg (fun y : ℝ => y ^ j) (by ring)
      _ = (4 : ℝ) ^ j * (x ^ 2 / 4) ^ j := mul_pow _ _ _
      _ ≤ (4 : ℝ) ^ j * (Real.exp (x ^ 2 / 4) * (j.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hsquare : (x ^ j) ^ 2 = (x ^ 2) ^ j := by
    calc
      (x ^ j) ^ 2 = x ^ (j * 2) := (pow_mul x j 2).symm
      _ = x ^ (2 * j) := by rw [Nat.mul_comm j 2]
      _ = (x ^ 2) ^ j := pow_mul x 2 j
  have hpower : x ^ j ≤ 1 + (x ^ 2) ^ j := by
    nlinarith [sq_nonneg (x ^ j - 1), pow_nonneg hx j, hsquare]
  calc
    x ^ j ≤ 1 + (x ^ 2) ^ j := hpower
    _ ≤ 1 + (4 : ℝ) ^ j * (j.factorial : ℝ) * Real.exp (x ^ 2 / 4) :=
      add_le_add_right hp' 1
    _ ≤ Real.exp (x ^ 2 / 4) +
        (4 : ℝ) ^ j * (j.factorial : ℝ) * Real.exp (x ^ 2 / 4) :=
      add_le_add_left (Real.one_le_exp (by positivity)) _
    _ = _ := by ring

/-- Gaussian-polynomial decay with the unchanged physical sqrt(j!)
normalization, derived for every actual natural jet degree. -/
theorem planeJet_gaussian_polynomial_decay (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x ^ 2 / 2) * x ^ j / Real.sqrt (j.factorial : ℝ) ≤
      planeJetPolynomialEnvelope j * Real.exp (-x ^ 2 / 4) := by
  calc
    _ ≤ Real.exp (-x ^ 2 / 2) *
        ((1 + (4 : ℝ) ^ j * (j.factorial : ℝ)) * Real.exp (x ^ 2 / 4)) /
          Real.sqrt (j.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (natPower_le_gaussian_growth j x hx)
          (Real.exp_nonneg _)) (Real.sqrt_nonneg _)
    _ = planeJetPolynomialEnvelope j *
        (Real.exp (-x ^ 2 / 2) * Real.exp (x ^ 2 / 4)) := by
      unfold planeJetPolynomialEnvelope
      ring
    _ = _ := by
      rw [← Real.exp_add, show -x ^ 2 / 2 + x ^ 2 / 4 = -x ^ 2 / 4 by ring]

/-- The exact original normalized entire seed, before either magnetic
translation or periodization. -/
def planeJetStrippedSeed (j : ℕ) (z : ℂ) : ℂ :=
  z ^ j / (Real.sqrt (j.factorial : ℝ) : ℂ)

theorem planeJetStrippedSeed_differentiable (j : ℕ) :
    Differentiable ℂ (planeJetStrippedSeed j) :=
  (differentiable_id.pow j).div_const _

/-- The exact entire factor of each original image, retaining the actual
inverse chi and both physical magnetic translations. -/
def planeJetStrippedImage (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ)
    (p : ℤ × ℤ) (z : ℂ) : ℂ :=
  (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹ *
    translatedStrippedFactor (latticePeriod G.omega1 G.omega2 p)
      (translatedStrippedFactor R (planeJetStrippedSeed j)) z

theorem planeJetStrippedImage_differentiable (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (p : ℤ × ℤ) :
    Differentiable ℂ (planeJetStrippedImage G theta j R p) := by
  exact (translatedStrippedFactor_differentiable _ _
    (translatedStrippedFactor_differentiable R _
      (planeJetStrippedSeed_differentiable j))).const_mul _

/-- Exact Gaussian stripping of the original physical j-image. -/
theorem planeJet_magneticImage_factor (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (p : ℤ × ℤ) (z : ℂ) :
    magneticImage G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (translatedPlaneJet j R) p z =
      gaussianFactor 1 z * planeJetStrippedImage G theta j R p z := by
  have hseed : ∀ w : ℂ, planeJet j w = gaussianFactor 1 w * planeJetStrippedSeed j w := by
    intro w
    unfold planeJet planeJetStrippedSeed
    ring
  have htranslated : ∀ w : ℂ, translatedPlaneJet j R w =
      gaussianFactor 1 w * translatedStrippedFactor R (planeJetStrippedSeed j) w :=
    magneticTranslate_stripped_factor R (planeJet j) (planeJetStrippedSeed j) hseed
  simp only [magneticImage, pow_one, Nat.cast_one]
  rw [magneticTranslate_stripped_factor _ _ _ htranslated z]
  unfold planeJetStrippedImage
  ring

/-- The actual image norm has the original translated argument and
polynomial/factorial normalization; all magnetic factors have unit modulus. -/
theorem planeJet_magneticImage_norm (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (p : ℤ × ℤ) (z : ℂ) :
    ‖magneticImage G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (translatedPlaneJet j R) p z‖ =
      Real.exp (-‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ 2 / 2) *
        ‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ j /
          Real.sqrt (j.factorial : ℝ) := by
  simp only [magneticImage, pow_one, Nat.cast_one, norm_mul, norm_inv,
    latticeChi_norm, inv_one, one_mul, magneticTranslate_norm,
    translatedPlaneJet, planeJet_norm]

/-- Exact stripped-image norm, derived by dividing the actual image
by its nonzero physical Gaussian factor. -/
theorem planeJetStrippedImage_norm (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (p : ℤ × ℤ) (z : ℂ) :
    ‖planeJetStrippedImage G theta j R p z‖ =
      Real.exp (‖z‖ ^ 2 / 2) *
        (Real.exp (-‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ 2 / 2) *
          ‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ j /
            Real.sqrt (j.factorial : ℝ)) := by
  have hf := congrArg (fun w : ℂ => ‖w‖) (planeJet_magneticImage_factor G theta j R p z)
  rw [norm_mul, gaussianFactor_one_norm] at hf
  have hd : ‖planeJetStrippedImage G theta j R p z‖ =
      ‖magneticImage G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
        (translatedPlaneJet j R) p z‖ / Real.exp (-‖z‖ ^ 2 / 2) := by
    apply (eq_div_iff (Real.exp_pos _).ne').mpr
    simpa only [mul_comm] using hf.symm
  rw [hd, planeJet_magneticImage_norm,
    show -‖z‖ ^ 2 / 2 = -(‖z‖ ^ 2 / 2) by ring, Real.exp_neg, div_inv_eq_mul]
  ring

/-- A derived local majorant for each original normalized jet degree.
Its polynomial coefficient depends on j and its ball coefficient on R,B. -/
def planeJetBallMajorant (G : Geometry) (j : ℕ) (R : ℂ) (B : ℝ)
    (p : ℤ × ℤ) : ℝ :=
  (planeJetPolynomialEnvelope j * Real.exp (B ^ 2 / 2 + (B + ‖R‖) ^ 2 / 4)) *
    Real.exp (-‖latticePeriod G.omega1 G.omega2 p‖ ^ 2 / 8)

theorem planeJetBallMajorant_summable (G : Geometry) (j : ℕ) (R : ℂ) (B : ℝ) :
    Summable (planeJetBallMajorant G j R B) :=
  (lattice_planeJet_gaussian_summable G).mul_left _

theorem planeJetStrippedImage_le_ballMajorant (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (B : ℝ) (hB : 0 ≤ B) (p : ℤ × ℤ) (z : ℂ) (hz : ‖z‖ ≤ B) :
    ‖planeJetStrippedImage G theta j R p z‖ ≤ planeJetBallMajorant G j R B p := by
  have hzsq : ‖z‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hu : ‖z - R‖ ≤ B + ‖R‖ :=
    (norm_sub_le z R).trans (add_le_add_left hz _)
  have husq : ‖z - R‖ ^ 2 ≤ (B + ‖R‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hl : ‖latticePeriod G.omega1 G.omega2 p‖ ≤
      ‖z - R‖ + ‖z - latticePeriod G.omega1 G.omega2 p - R‖ := by
    have h := norm_sub_le (z - R) (z - latticePeriod G.omega1 G.omega2 p - R)
    rw [show (z - R) - (z - latticePeriod G.omega1 G.omega2 p - R) =
      latticePeriod G.omega1 G.omega2 p by ring] at h
    exact h
  have hlsq := pow_le_pow_left₀
    (norm_nonneg (latticePeriod G.omega1 G.omega2 p)) hl 2
  have hsplit : ‖latticePeriod G.omega1 G.omega2 p‖ ^ 2 ≤
      2 * ‖z - R‖ ^ 2 + 2 * ‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖z - R‖ - ‖z - latticePeriod G.omega1 G.omega2 p - R‖)]
  have hexp :
      Real.exp (‖z‖ ^ 2 / 2) *
        Real.exp (-‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ 2 / 4) ≤
      Real.exp (B ^ 2 / 2 + (B + ‖R‖) ^ 2 / 4) *
        Real.exp (-‖latticePeriod G.omega1 G.omega2 p‖ ^ 2 / 8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [planeJetStrippedImage_norm]
  calc
    _ ≤ Real.exp (‖z‖ ^ 2 / 2) *
        (planeJetPolynomialEnvelope j *
          Real.exp (-‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_left
        (planeJet_gaussian_polynomial_decay j _ (norm_nonneg _)) (Real.exp_nonneg _)
    _ = planeJetPolynomialEnvelope j *
        (Real.exp (‖z‖ ^ 2 / 2) *
          Real.exp (-‖z - latticePeriod G.omega1 G.omega2 p - R‖ ^ 2 / 4)) := by ring
    _ ≤ planeJetPolynomialEnvelope j *
        (Real.exp (B ^ 2 / 2 + (B + ‖R‖) ^ 2 / 4) *
          Real.exp (-‖latticePeriod G.omega1 G.omega2 p‖ ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left hexp (planeJetPolynomialEnvelope_nonneg j)
    _ = planeJetBallMajorant G j R B p := by unfold planeJetBallMajorant; ring

/-- Uniform convergence of the exact entire stripped image series on
every finite closed ball for every original natural jet index. -/
theorem planeJetStrippedImages_tendstoUniformlyOn (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (B : ℝ) (hB : 0 ≤ B) :
    TendstoUniformlyOn
      (fun s : Finset (ℤ × ℤ) => fun z => ∑ p ∈ s, planeJetStrippedImage G theta j R p z)
      (fun z => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p z)
      atTop (Metric.closedBall (0 : ℂ) B) := by
  apply tendstoUniformlyOn_tsum (planeJetBallMajorant_summable G j R B)
  intro p z hz
  apply planeJetStrippedImage_le_ballMajorant G theta j R B hB p z
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

theorem planeJet_magneticImage_le_stripped (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (p : ℤ × ℤ) (z : ℂ) :
    ‖magneticImage G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (translatedPlaneJet j R) p z‖ ≤ ‖planeJetStrippedImage G theta j R p z‖ := by
  rw [planeJet_magneticImage_factor, norm_mul, gaussianFactor_one_norm]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖z‖]

/-- Uniform convergence of the original physical image series on each
finite closed ball, with the exact rawJetFunction as its limit. -/
theorem planeJetImages_tendstoUniformlyOn (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (B : ℝ) (hB : 0 ≤ B) :
    TendstoUniformlyOn
      (fun s : Finset (ℤ × ℤ) => fun z => ∑ p ∈ s,
        magneticImage G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
          (translatedPlaneJet j R) p z)
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R)
      atTop (Metric.closedBall (0 : ℂ) B) := by
  apply tendstoUniformlyOn_tsum (planeJetBallMajorant_summable G j R B)
  intro p z hz
  apply (planeJet_magneticImage_le_stripped G theta j R p z).trans
  apply planeJetStrippedImage_le_ballMajorant G theta j R B hB p z
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

/-- The original convergence predicate is proved for every actual
translated canonical plane jet, rather than supplied as a new input. -/
theorem translatedPlaneJet_hasAbsolutelySummableImages (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) : HasAbsolutelySummableImages G.M 1 G.omega1 G.omega2
      theta.theta1 theta.theta2 (translatedPlaneJet j R) := by
  intro z
  exact (planeJetBallMajorant_summable G j R ‖z‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p =>
      (planeJet_magneticImage_le_stripped G theta j R p z).trans
        (planeJetStrippedImage_le_ballMajorant G theta j R ‖z‖ (norm_nonneg _) p z le_rfl))

/-- The exact stripped sum is entire by the derived finite-ball majorant,
for every natural jet degree and every legal geometry and twist. -/
theorem planeJetStrippedSum_differentiable (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) :
    Differentiable ℂ (fun z => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p z) := by
  intro z
  let B : ℝ := ‖z‖ + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hz : z ∈ Metric.ball (0 : ℂ) B := by
    simp only [Metric.mem_ball, dist_zero_right]
    dsimp [B]
    linarith
  have hd : DifferentiableOn ℂ
      (fun w => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p w)
      (Metric.ball (0 : ℂ) B) := Complex.differentiableOn_tsum_of_summable_norm
    (planeJetBallMajorant_summable G j R B)
    (fun p => (planeJetStrippedImage_differentiable G theta j R p).differentiableOn)
    Metric.isOpen_ball (fun p w hw =>
      planeJetStrippedImage_le_ballMajorant G theta j R B hB p w
        (by
          have hn : ‖w‖ < B := by
            simpa only [Metric.mem_ball, dist_zero_right] using hw
          exact hn.le))
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)

/-- The original all-j raw periodizer has its exact entire stripped
factor, with no alteration to the Gaussian or factorial normalization. -/
theorem rawPlaneJet_isGaussianHolomorphic (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) : IsGaussianHolomorphic 1
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R) := by
  refine ⟨fun z => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p z,
    planeJetStrippedSum_differentiable G theta j R, ?_⟩
  intro z
  change (∑' p : ℤ × ℤ, magneticImage G.M 1 G.omega1 G.omega2
    theta.theta1 theta.theta2 (translatedPlaneJet j R) p z) = _
  simp_rw [planeJet_magneticImage_factor]
  exact tsum_mul_left

/-- Original charge-one RawLLL membership for every natural jet degree,
using the derived analytic condition and the original boundary law. -/
theorem rawPlaneJet_mem_RawLLL (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    IsGaussianHolomorphic 1
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R) ∧
      HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R) :=
  ⟨rawPlaneJet_isGaussianHolomorphic G theta j R,
    magneticPeriodization_boundary G.M 1 G.omega1 G.omega2 (legal_area G)
      theta.theta1 theta.theta2 (translatedPlaneJet j R)⟩

/-- The original all-j raw periodizer in the existing actual cell-Hilbert
carrier, entered only after its original RawLLL membership is proved. -/
def rawPlaneJet (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) : LLL G theta 1 :=
  ⟨rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R,
    by
      simpa [rawLLLSubmodule] using rawPlaneJet_mem_RawLLL G theta j R⟩

theorem rawPlaneJet_val (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    (rawPlaneJet G theta j R).val =
      rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R := rfl

/-- Every actual pair of raw jets has its original cell cross-integral
domain, derived from proved continuous raw sections. This is not a Gram
value formula or a derivative reproducing identity. -/
theorem rawPlaneJets_cell_cross_integrable (G : Geometry) (theta : Twist)
    (j m : ℕ) (R S : ℂ) :
    Integrable (fun z =>
      conj (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R z) *
        rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 m S z)
      (cellMeasure G 1) :=
  rawCellInner_integrable G theta 1 (rawPlaneJet G theta j R) (rawPlaneJet G theta m S)

/-- The original physical cell norm integrand is integrable for every
canonical jet, without a supplied numerical norm budget. -/
theorem rawPlaneJet_cell_norm_sq_integrable (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) :
    Integrable (fun z =>
      ‖rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R z‖ ^ 2)
      (cellMeasure G 1) :=
  continuous_integrable_cellMeasure G 1
    ((rawLLL_continuous G theta 1 (rawPlaneJet G theta j R)).norm.pow 2)

#print axioms exp_neg_sq_div_eight_le_inv_pow
#print axioms lattice_planeJet_gaussian_summable
#print axioms planeJet_scale_pos
#print axioms planeJetPolynomialEnvelope_nonneg
#print axioms natPower_le_gaussian_growth
#print axioms planeJet_gaussian_polynomial_decay
#print axioms planeJetStrippedSeed_differentiable
#print axioms planeJetStrippedImage_differentiable
#print axioms planeJet_magneticImage_factor
#print axioms planeJet_magneticImage_norm
#print axioms planeJetStrippedImage_norm
#print axioms planeJetBallMajorant_summable
#print axioms planeJetStrippedImage_le_ballMajorant
#print axioms planeJetStrippedImages_tendstoUniformlyOn
#print axioms planeJet_magneticImage_le_stripped
#print axioms planeJetImages_tendstoUniformlyOn
#print axioms translatedPlaneJet_hasAbsolutelySummableImages
#print axioms planeJetStrippedSum_differentiable
#print axioms rawPlaneJet_isGaussianHolomorphic
#print axioms rawPlaneJet_mem_RawLLL
#print axioms rawPlaneJet
#print axioms rawPlaneJet_val
#print axioms rawPlaneJets_cell_cross_integrable
#print axioms rawPlaneJet_cell_norm_sq_integrable

end TorusLean.Shared.PlaneJetMembership
