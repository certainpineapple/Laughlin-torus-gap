import torus.geometry.Jacobi
import PairNormalSlice
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
The canonical physical covariant jet, on an actual Gaussian-holomorphic pair
function, equals the ordinary normal derivative of its holomorphic factor.
The same physical Gaussian and original scalar normalization are retained.
These are local universal-cover identities; the contact Hamiltonian, its
kernel-to-zero-jet implication, joint division and COM descent are not inputs
that are silently discharged by this module.
-/

set_option autoImplicit false

noncomputable section
namespace TorusLean.Shared.NormalJetBridge

open TorusLean.Geometry
open TorusLean.Geometry.JastrowDivision
open Filter
open scoped Topology ComplexConjugate BigOperators

/-- The original normalization, before division. -/
def jetScale (a b : ℝ) (d : ℕ) : ℂ :=
  (Real.sqrt (relativeCharge a b ^ d * (d.factorial : ℝ)) : ℂ)

theorem jetScale_ne_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (d : ℕ) :
    jetScale a b d ≠ 0 := by
  have h : 0 < relativeCharge a b ^ d * (d.factorial : ℝ) :=
    mul_pos (pow_pos (relativeCharge_pos a b ha hb) d)
      (Nat.cast_pos.mpr (Nat.factorial_pos d))
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr h))

/-- Exact Gaussian cancellation inside the canonical iterated derivative.
No assumption that the physical Gaussian-containing function is holomorphic
is made. A fixed nonzero spectator Gaussian may be included in `S`. -/
theorem localNormalJet_gaussian_factor (a b : ℝ) (hab : a + b ≠ 0)
    (d : ℕ) (Ψ F : ℂ × ℂ → ℂ) (S : ℂ)
    (hΨ : ∀ z, Ψ z = S * (gaussianFactor a z.1 * gaussianFactor b z.2) * F z)
    (C : ℂ) :
    localNormalJet a b d Ψ C =
      (jetScale a b d)⁻¹ * (S * gaussianFactor (a + b) C) *
        iteratedDeriv d (fun r : ℂ => F (jacobiFirst a b C r, jacobiSecond a b C r)) 0 := by
  have hfun : (fun r : ℂ =>
      Complex.exp ((relativeCharge a b : ℂ) * (r * conj r) / 2) *
        Ψ (jacobiFirst a b C r, jacobiSecond a b C r)) =
      (fun r : ℂ => (S * gaussianFactor (a + b) C) *
        F (jacobiFirst a b C r, jacobiSecond a b C r)) := by
    funext r
    rw [hΨ]
    calc
      _ = S * (Complex.exp ((relativeCharge a b : ℂ) * (r * conj r) / 2) *
        (gaussianFactor a (jacobiFirst a b C r) *
          gaussianFactor b (jacobiSecond a b C r))) *
        F (jacobiFirst a b C r, jacobiSecond a b C r) := by ring
      _ = _ := by rw [jacobi_covariant_gaussian_cancel a b hab]
  unfold localNormalJet
  rw [hfun, iteratedDeriv_const_mul_field]
  simp only [jetScale]
  ring

/-- The scalar prefactor is proved nonzero from actual positive charges and
nonzero spectator Gaussians, so vanishing jets are equivalent in both directions. -/
theorem localNormalJet_zero_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (d : ℕ) (Ψ F : ℂ × ℂ → ℂ) (S : ℂ) (hS : S ≠ 0)
    (hΨ : ∀ z, Ψ z = S * (gaussianFactor a z.1 * gaussianFactor b z.2) * F z)
    (C : ℂ) :
    localNormalJet a b d Ψ C = 0 ↔
      iteratedDeriv d (fun r : ℂ => F (jacobiFirst a b C r, jacobiSecond a b C r)) 0 = 0 := by
  rw [localNormalJet_gaussian_factor a b (ne_of_gt (add_pos ha hb)) d Ψ F S hΨ C]
  exact mul_eq_zero.trans (or_iff_right
    (mul_ne_zero (inv_ne_zero (jetScale_ne_zero a b ha hb d))
      (mul_ne_zero hS (gaussianFactor_ne_zero (a + b) C))))

theorem equal_charge_coordinates (C r : ℂ) :
    jacobiFirst 1 1 C r = C + r / 2 ∧ jacobiSecond 1 1 C r = C - r / 2 := by
  constructor <;> simp [jacobiFirst, jacobiSecond] <;> ring

/-- In the equal-charge physical chart, every covariant jet has exactly the
ordinary normal-slice vanishing condition, including degree zero and one. -/
theorem equal_charge_jet_zero_iff (d : ℕ) (Ψ F : ℂ × ℂ → ℂ)
    (S : ℂ) (hS : S ≠ 0)
    (hΨ : ∀ z, Ψ z = S * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) * F z)
    (C : ℂ) :
    localNormalJet 1 1 d Ψ C = 0 ↔ iteratedDeriv d (pairNormalSlice F C) 0 = 0 := by
  have hfun : (fun r : ℂ => F (jacobiFirst 1 1 C r, jacobiSecond 1 1 C r)) =
      pairNormalSlice F C := by
    funext r
    rw [(equal_charge_coordinates C r).1, (equal_charge_coordinates C r).2]
    rfl
  rw [← hfun]
  exact localNormalJet_zero_iff 1 1 (by norm_num) (by norm_num) d Ψ F S hS hΨ C

/-- Physical antisymmetry passes to the holomorphic factor because all
Gaussian factors are nonzero; no statistics premise on F is added. -/
theorem holomorphic_factor_antisymmetric (Ψ F : ℂ × ℂ → ℂ)
    (S : ℂ) (hS : S ≠ 0)
    (hΨ : ∀ z, Ψ z = S * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) * F z)
    (hstats : ∀ x y, Ψ (y, x) = -Ψ (x, y)) :
    ∀ x y, F (y, x) = -F (x, y) := by
  intro x y
  have h := hstats x y
  rw [hΨ, hΨ, mul_comm (gaussianFactor 1 y) (gaussianFactor 1 x), ← mul_neg] at h
  exact mul_left_cancel₀ (mul_ne_zero hS
    (mul_ne_zero (gaussianFactor_ne_zero 1 x) (gaussianFactor_ne_zero 1 y))) h

theorem holomorphic_factor_symmetric (Ψ F : ℂ × ℂ → ℂ)
    (S : ℂ) (hS : S ≠ 0)
    (hΨ : ∀ z, Ψ z = S * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) * F z)
    (hstats : ∀ x y, Ψ (y, x) = Ψ (x, y)) :
    ∀ x y, F (y, x) = F (x, y) := by
  intro x y
  have h := hstats x y
  rw [hΨ, hΨ, mul_comm (gaussianFactor 1 y) (gaussianFactor 1 x)] at h
  exact mul_left_cancel₀ (mul_ne_zero hS
    (mul_ne_zero (gaussianFactor_ne_zero 1 x) (gaussianFactor_ne_zero 1 y))) h

/-- Original degree-one physical contact jet plus physical fermionic
statistics yields a local cubic divisor of the actual holomorphic factor.
Existence of the quotient is a conclusion, for each fixed COM/spectator. -/
theorem fermionic_physical_jet_local_cubic_division (Ψ F : ℂ × ℂ → ℂ)
    (S : ℂ) (hS : S ≠ 0)
    (hΨ : ∀ z, Ψ z = S * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) * F z)
    (hstats : ∀ x y, Ψ (y, x) = -Ψ (x, y)) (C : ℂ)
    (hF : AnalyticAt ℂ F (C, C)) (hcontact : localNormalJet 1 1 1 Ψ C = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ r in 𝓝 0, F (C + r / 2, C - r / 2) = r ^ 3 * q r := by
  apply antisymmetric_pair_contact_local_division F C hF
    (holomorphic_factor_antisymmetric Ψ F S hS hΨ hstats)
  simpa only [iteratedDeriv_one] using (equal_charge_jet_zero_iff 1 Ψ F S hS hΨ C).mp hcontact

/-- Original degree-zero bosonic contact jet and physical exchange symmetry
produce the quadratic divisor in the same physical convention. -/
theorem bosonic_physical_jet_local_quadratic_division (Ψ F : ℂ × ℂ → ℂ)
    (S : ℂ) (hS : S ≠ 0)
    (hΨ : ∀ z, Ψ z = S * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) * F z)
    (hstats : ∀ x y, Ψ (y, x) = Ψ (x, y)) (C : ℂ)
    (hF : AnalyticAt ℂ F (C, C)) (hcontact : localNormalJet 1 1 0 Ψ C = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ r in 𝓝 0, F (C + r / 2, C - r / 2) = r ^ 2 * q r := by
  apply symmetric_pair_contact_local_division F C hF
    (holomorphic_factor_symmetric Ψ F S hS hΨ hstats)
  have h := (equal_charge_jet_zero_iff 0 Ψ F S hS hΨ C).mp hcontact
  simpa [pairNormalSlice] using h

/-- Actual product of charge-one Gaussians at arbitrary fixed spectator
coordinates. The empty product includes the two-particle case. -/
def spectatorGaussian {ι : Type*} [Fintype ι] (s : ι → ℂ) : ℂ :=
  ∏ i, gaussianFactor 1 (s i)

theorem spectatorGaussian_ne_zero {ι : Type*} [Fintype ι] (s : ι → ℂ) :
    spectatorGaussian s ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => gaussianFactor_ne_zero 1 (s i))

/-- A universal-cover pair slice of the physical Gaussian-times-holomorphic
wavefunction, with all spectator Gaussians retained. This is an evaluation
formula, not a competing definition of the Hilbert space or Hamiltonian. -/
def pairWithSpectators {ι : Type*} [Fintype ι] (s : ι → ℂ)
    (F : ℂ × ℂ → ℂ) (z : ℂ × ℂ) : ℂ :=
  spectatorGaussian s * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) * F z

theorem spectator_pair_jet_zero_iff {ι : Type*} [Fintype ι] (s : ι → ℂ)
    (F : ℂ × ℂ → ℂ) (d : ℕ) (C : ℂ) :
    localNormalJet 1 1 d (pairWithSpectators s F) C = 0 ↔
      iteratedDeriv d (pairNormalSlice F C) 0 = 0 :=
  equal_charge_jet_zero_iff d _ F (spectatorGaussian s)
    (spectatorGaussian_ne_zero s) (fun _ => rfl) C

/-- No spectator nonvanishing or quotient-existence premise is needed:
the actual Gaussian product supplies nonvanishing, and analytic division
produces the quotient from the original physical contact jet. -/
theorem fermionic_spectator_contact_local_division {ι : Type*} [Fintype ι]
    (s : ι → ℂ) (F : ℂ × ℂ → ℂ)
    (hstats : ∀ x y, pairWithSpectators s F (y, x) =
      -pairWithSpectators s F (x, y)) (C : ℂ)
    (hF : AnalyticAt ℂ F (C, C))
    (hcontact : localNormalJet 1 1 1 (pairWithSpectators s F) C = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ r in 𝓝 0, F (C + r / 2, C - r / 2) = r ^ 3 * q r :=
  fermionic_physical_jet_local_cubic_division _ F (spectatorGaussian s)
    (spectatorGaussian_ne_zero s) (fun _ => rfl) hstats C hF hcontact

theorem bosonic_spectator_contact_local_division {ι : Type*} [Fintype ι]
    (s : ι → ℂ) (F : ℂ × ℂ → ℂ)
    (hstats : ∀ x y, pairWithSpectators s F (y, x) =
      pairWithSpectators s F (x, y)) (C : ℂ)
    (hF : AnalyticAt ℂ F (C, C))
    (hcontact : localNormalJet 1 1 0 (pairWithSpectators s F) C = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ r in 𝓝 0, F (C + r / 2, C - r / 2) = r ^ 2 * q r :=
  bosonic_physical_jet_local_quadratic_division _ F (spectatorGaussian s)
    (spectatorGaussian_ne_zero s) (fun _ => rfl) hstats C hF hcontact

end TorusLean.Shared.NormalJetBridge
