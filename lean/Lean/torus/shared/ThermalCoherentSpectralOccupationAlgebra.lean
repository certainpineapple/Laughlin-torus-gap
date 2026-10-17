import UnitaryTransport
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Finite-basis transport of a genuine one-particle kernel identity to the
unchanged factorial occupation core. The annihilation operator remains
conjugate-linear in its mode. This generic composition lemma exposes both
the scalar kernel identity and its real integrability domain; a separate
physical module discharges them for the original raw torus jets. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSpectralOccupation
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two mode indices are reversed relative to a conjugate-first orbital
kernel, because modeAnnihilate itself is conjugate-linear in the mode. -/
theorem modeAnnihilate_inner_expansion (u : Orbital ι) (p q : Core ι ℂ) :
    occupationInner (fun _ => 1) (modeAnnihilate u p) (modeAnnihilate u q) =
      ∑ i, ∑ k, u i * conj (u k) *
        occupationInner (fun _ => 1) (annihilate i p) (annihilate k q) := by
  simp only [modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [canonical_inner_sum_left]
  simp only [occupationInner_smul_left, canonical_inner_sum_right,
    occupationInner_smul_right, star_star, Complex.star_def, Complex.conj_conj,
    Finset.mul_sum, mul_assoc]

theorem weighted_modeAnnihilate_inner_expansion (w : ℝ) (u : Orbital ι) (p q : Core ι ℂ) :
    (w : ℂ) * occupationInner (fun _ => 1) (modeAnnihilate u p) (modeAnnihilate u q) =
      ∑ i, ∑ k, ((w : ℂ) * conj (u k) * u i) *
        occupationInner (fun _ => 1) (annihilate i p) (annihilate k q) := by
  rw [modeAnnihilate_inner_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

section Spectral
variable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (u : X → Orbital ι)

theorem weighted_modeAnnihilate_cross_integrable
    (hdom : ∀ i k, Integrable (fun x => (w x : ℂ) * conj (u x k) * u x i) μ)
    (p q : Core ι ℂ) :
    Integrable (fun x => (w x : ℂ) *
      occupationInner (fun _ => 1) (modeAnnihilate (u x) p) (modeAnnihilate (u x) q)) μ := by
  simp_rw [weighted_modeAnnihilate_inner_expansion]
  apply integrable_finsetSum
  intro i hi
  exact integrable_finsetSum _ (fun k hk => (hdom i k).mul_const _)

/-- Finite linear combinations of honest scalar HasSum identities produce the
whole-core cross form. No positivity or occupation cutoff is assumed. -/
theorem weighted_modeAnnihilate_cross_hasSum (v : ℕ → Orbital ι) (lam : ℕ → ℝ)
    (hdom : ∀ i k, Integrable (fun x => (w x : ℂ) * conj (u x k) * u x i) μ)
    (hkernel : ∀ i k, HasSum (fun j => (lam j : ℂ) * conj (v j k) * v j i)
      (∫ x, (w x : ℂ) * conj (u x k) * u x i ∂μ)) (p q : Core ι ℂ) :
    HasSum (fun j => (lam j : ℂ) *
      occupationInner (fun _ => 1) (modeAnnihilate (v j) p) (modeAnnihilate (v j) q))
      (∫ x, (w x : ℂ) *
        occupationInner (fun _ => 1) (modeAnnihilate (u x) p) (modeAnnihilate (u x) q) ∂μ) := by
  have hs := hasSum_sum (s := (Finset.univ : Finset ι)) (fun i _ =>
    hasSum_sum (s := (Finset.univ : Finset ι)) (fun k _ =>
      (hkernel i k).mul_right
        (occupationInner (fun _ => 1) (annihilate i p) (annihilate k q))))
  convert hs using 1
  · funext j
    exact weighted_modeAnnihilate_inner_expansion (lam j) (v j) p q
  · simp_rw [weighted_modeAnnihilate_inner_expansion]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      · simp only [integral_mul_const]
      · intro k hk
        exact (hdom i k).mul_const _
    · intro i hi
      exact integrable_finsetSum _ (fun k hk => (hdom i k).mul_const _)

theorem weighted_modeAnnihilate_normSq_integrable
    (hdom : ∀ i k, Integrable (fun x => (w x : ℂ) * conj (u x k) * u x i) μ)
    (p : Core ι ℂ) :
    Integrable (fun x => w x * occupationMetricNormSq (fun _ => 1) (modeAnnihilate (u x) p)) μ := by
  have h := (weighted_modeAnnihilate_cross_integrable μ w u hdom p p).re
  apply h.congr
  apply Filter.Eventually.of_forall
  intro x
  change ((w x : ℂ) * occupationInner (fun _ => 1)
    (modeAnnihilate (u x) p) (modeAnnihilate (u x) p)).re = _
  rw [occupationInner_self, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The actual occupation norm spectrum follows from the full complex cross
form, preserving every repeated-mode factorial in the original inner product. -/
theorem weighted_modeAnnihilate_normSq_hasSum (v : ℕ → Orbital ι) (lam : ℕ → ℝ)
    (hdom : ∀ i k, Integrable (fun x => (w x : ℂ) * conj (u x k) * u x i) μ)
    (hkernel : ∀ i k, HasSum (fun j => (lam j : ℂ) * conj (v j k) * v j i)
      (∫ x, (w x : ℂ) * conj (u x k) * u x i ∂μ)) (p : Core ι ℂ) :
    HasSum (fun j => lam j * occupationMetricNormSq (fun _ => 1) (modeAnnihilate (v j) p))
      (∫ x, w x * occupationMetricNormSq (fun _ => 1) (modeAnnihilate (u x) p) ∂μ) := by
  have h := weighted_modeAnnihilate_cross_hasSum μ w u v lam hdom hkernel p p
  simp_rw [occupationInner_self, ← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal] at h
  exact Complex.hasSum_ofReal.mp h

end Spectral
end TorusLean.Shared.ThermalCoherentSpectralOccupation
