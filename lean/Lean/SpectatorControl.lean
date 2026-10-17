import UnitaryTransport

/-!
Nonorthogonal double spectator control on the actual shared polynomial core.
The main bound has no contact-H budget and no particle-number factor.
The torus coherent/contact identifications remain separate obligations.
-/

set_option autoImplicit false
namespace TorusLean.Boson.SpectatorControl

open scoped BigOperators ComplexConjugate
open TorusLean.Boson TorusLean.Boson.UnitaryTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
noncomputable section

abbrev q (f : Core ι ℂ) : ℝ := occupationMetricNormSq (fun _ => 1) f
abbrev ip (f g : Core ι ℂ) : ℂ := occupationInner (fun _ => 1) f g

def modeNumber (β : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  (modeCreate β).comp (modeAnnihilate β)

/-- Ordering matches the paper: A = a(γ) a(β). No Sym² factor is included. -/
def spectatorPair (β γ : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  (modeAnnihilate γ).comp (modeAnnihilate β)

theorem canonical_normSq_smul (c : ℂ) (f : Core ι ℂ) :
    q (c • f) = Complex.normSq c * q f :=
  TorusLean.BosonBridge.OccupationInstance.metricNormSq_smul
    (fun _ => 1) c f (Classical.arbitrary ι)

theorem canonical_inner_real_symm (f g : Core ι ℂ) : (ip g f).re = (ip f g).re := by
  have h := congrArg Complex.re (occupationInner_conj_symm (fun _ : ι => 1) f g)
  simpa [Complex.star_def] using h.symm

theorem canonical_normSq_sub (f g : Core ι ℂ) :
    q (f - g) = q f + q g - 2 * (ip f g).re := by
  unfold q ip
  rw [← occupationInner_self_re]
  simp only [sub_eq_add_neg, ← neg_one_smul ℂ g, occupationInner_add_left,
    occupationInner_add_right, occupationInner_smul_left, occupationInner_smul_right]
  simp only [star_neg, star_one, neg_mul, one_mul, mul_neg, mul_one,
    Complex.add_re, Complex.neg_re, neg_neg, occupationInner_self_re]
  rw [show (occupationInner (fun _ => 1) g f).re =
    (occupationInner (fun _ => 1) f g).re from canonical_inner_real_symm f g]
  ring

theorem canonical_inner_real_young (f g : Core ι ℂ) :
    (ip f g).re ≤ (q f + q g) / 2 := by
  have h := occupationMetricNormSq_nonneg (fun _ => 1) (f - g)
  change 0 ≤ q (f - g) at h
  rw [canonical_normSq_sub] at h
  linarith

/-- Retains the complex overlap phase until after the real quadratic-form
estimate. No orthogonality assumption is used. -/
theorem canonical_negative_cross_weighted (ω : ℂ) (f g : Core ι ℂ) :
    -(ω * ip f g).re ≤ (q f + Complex.normSq ω * q g) / 2 := by
  have h := canonical_inner_real_young f ((-ω) • g)
  have hi : ip f ((-ω) • g) = (-ω) * ip f g :=
    occupationInner_smul_right (fun _ => 1) (-ω) f g
  rw [hi, canonical_normSq_smul] at h
  simpa only [neg_mul, Complex.neg_re, Complex.normSq_neg] using h

theorem canonical_negative_cross_control (ω : ℂ) (hω : ‖ω‖ ≤ 1) (f g : Core ι ℂ) :
    -(ω * ip f g).re ≤ (q f + q g) / 2 := by
  have h := canonical_negative_cross_weighted ω f g
  have hωsq : Complex.normSq ω ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg ω]
  have hq : Complex.normSq ω * q g ≤ q g := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hωsq (occupationMetricNormSq_nonneg (fun _ => 1) g)
  linarith

theorem mode_annihilate_adjoint (β : Orbital ι) (f g : Core ι ℂ) :
    ip (modeAnnihilate β f) g = ip f (modeCreate β g) := by
  have h := congrArg star (mode_create_adjoint β g f)
  simpa only [occupationInner_conj_symm] using h.symm

theorem mode_annihilate_commute (β γ : Orbital ι) (f : Core ι ℂ) :
    modeAnnihilate β (modeAnnihilate γ f) =
      modeAnnihilate γ (modeAnnihilate β f) := by
  simp only [modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [annihilate_commute]
  exact smul_comm _ _ _

/-- Complex CCR identity, with the nonorthogonal coherence term explicit. -/
theorem spectator_number_cross_identity (β γ : Orbital ι) (f : Core ι ℂ) :
    ip (modeNumber β f) (modeNumber γ f) =
      (q (spectatorPair β γ f) : ℂ) +
        (inner ℂ β γ) * ip (modeAnnihilate β f) (modeAnnihilate γ f) := by
  calc
    ip (modeNumber β f) (modeNumber γ f) =
        ip (modeAnnihilate β f)
          (modeAnnihilate β (modeCreate γ (modeAnnihilate γ f))) :=
      mode_create_adjoint β _ _
    _ = ip (modeAnnihilate β f)
        (modeCreate γ (modeAnnihilate β (modeAnnihilate γ f)) +
          (inner ℂ β γ) • modeAnnihilate γ f) := by rw [mode_mixed_ccr]
    _ = ip (modeAnnihilate β f)
          (modeCreate γ (modeAnnihilate β (modeAnnihilate γ f))) +
        (inner ℂ β γ) * ip (modeAnnihilate β f) (modeAnnihilate γ f) := by
      simp only [ip, occupationInner_add_right, occupationInner_smul_right]
    _ = ip (modeAnnihilate γ (modeAnnihilate β f))
          (modeAnnihilate β (modeAnnihilate γ f)) +
        (inner ℂ β γ) * ip (modeAnnihilate β f) (modeAnnihilate γ f) := by
      rw [← mode_annihilate_adjoint]
    _ = _ := by
      rw [mode_annihilate_commute β γ f]
      exact congrArg (fun z => z + (inner ℂ β γ) *
        ip (modeAnnihilate β f) (modeAnnihilate γ f))
          (occupationInner_self (fun _ => 1) (spectatorPair β γ f))

theorem spectator_number_cross_real (β γ : Orbital ι) (f : Core ι ℂ) :
    q (spectatorPair β γ f) = (ip (modeNumber β f) (modeNumber γ f)).re -
      ((inner ℂ β γ) * ip (modeAnnihilate β f) (modeAnnihilate γ f)).re := by
  have h := congrArg Complex.re (spectator_number_cross_identity β γ f)
  simp only [Complex.add_re, Complex.ofReal_re] at h
  linarith

theorem unit_orbital_inner_self (β : Orbital ι) (hβ : ‖β‖ = 1) : inner ℂ β β = 1 := by
  simp only [inner_self_eq_norm_sq_to_K, hβ, one_pow, RCLike.ofReal_one]

theorem mode_number_normSq (β : Orbital ι) (hβ : ‖β‖ = 1) (f : Core ι ℂ) :
    q (modeNumber β f) =
      q (modeAnnihilate β (modeAnnihilate β f)) + q (modeAnnihilate β f) := by
  have h := spectator_number_cross_real β β f
  rw [unit_orbital_inner_self β hβ, one_mul] at h
  have hn : (ip (modeNumber β f) (modeNumber β f)).re = q (modeNumber β f) :=
    occupationInner_self_re (fun _ => 1) _
  have ha : (ip (modeAnnihilate β f) (modeAnnihilate β f)).re = q (modeAnnihilate β f) :=
    occupationInner_self_re (fun _ => 1) _
  rw [hn, ha] at h
  change q (modeAnnihilate β (modeAnnihilate β f)) = _ at h
  linarith

theorem mode_double_annihilation_normSq (β : Orbital ι) (f : Core ι ℂ) :
    q (modeAnnihilate β (modeAnnihilate β f)) = 2 * q (modePair β f) := by
  have hs : Complex.normSq ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h := canonical_normSq_smul ((Real.sqrt 2)⁻¹ : ℂ)
    (modeAnnihilate β (modeAnnihilate β f))
  change q (modePair β f) = _ at h
  rw [hs] at h
  linarith

theorem unit_mode_number_pair_identity (β : Orbital ι) (hβ : ‖β‖ = 1) (f : Core ι ℂ) :
    q (modeNumber β f) = 2 * q (modePair β f) + q (modeAnnihilate β f) := by
  rw [mode_number_normSq β hβ, mode_double_annihilation_normSq]

/-- General complex-overlap estimate; its normSq overlap coefficient is
retained even when the modes are not normalized. -/
theorem two_spectator_overlap_control (β γ : Orbital ι) (f : Core ι ℂ) :
    q (spectatorPair β γ f) ≤
      (q (modeNumber β f) + q (modeNumber γ f) + q (modeAnnihilate β f) +
        Complex.normSq (inner ℂ β γ) * q (modeAnnihilate γ f)) / 2 := by
  have hnum := canonical_inner_real_young (modeNumber β f) (modeNumber γ f)
  have hcross := canonical_negative_cross_weighted (inner ℂ β γ)
    (modeAnnihilate β f) (modeAnnihilate γ f)
  rw [spectator_number_cross_real]
  linarith

/-- Paper's first double-spectator inequality, on the actual core. -/
theorem two_spectator_number_control (β γ : Orbital ι)
    (hβ : ‖β‖ = 1) (hγ : ‖γ‖ = 1) (f : Core ι ℂ) :
    q (spectatorPair β γ f) ≤
      (q (modeNumber β f) + q (modeNumber γ f) +
        q (modeAnnihilate β f) + q (modeAnnihilate γ f)) / 2 := by
  have hω : ‖inner ℂ β γ‖ ≤ 1 := by
    simpa only [hβ, hγ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) β γ
  have hnum := canonical_inner_real_young (modeNumber β f) (modeNumber γ f)
  have hcross := canonical_negative_cross_control (inner ℂ β γ) hω
    (modeAnnihilate β f) (modeAnnihilate γ f)
  rw [spectator_number_cross_real]
  linarith

/-- Uniform double-spectator control, including nonorthogonal modes.
No physical Hamiltonian, external budget, or occupation bound is assumed. -/
theorem two_spectator_pair_control (β γ : Orbital ι)
    (hβ : ‖β‖ = 1) (hγ : ‖γ‖ = 1) (f : Core ι ℂ) :
    q (spectatorPair β γ f) ≤
      2 * q (modePair β f) + 2 * q (modePair γ f) + 2 * q f := by
  have h := two_spectator_number_control β γ hβ hγ f
  rw [unit_mode_number_pair_identity β hβ, unit_mode_number_pair_identity γ hγ] at h
  have hb := normalized_mode_occupation_control β hβ f
  have hg := normalized_mode_occupation_control γ hγ f
  linarith

/-- This is only a budget-substitution corollary. Identifying E with a
physical contact form and proving both pair budgets are separate duties. -/
theorem two_spectator_given_pair_budget (β γ : Orbital ι)
    (hβ : ‖β‖ = 1) (hγ : ‖γ‖ = 1) (f : Core ι ℂ) (E : ℝ)
    (hβpair : q (modePair β f) ≤ E) (hγpair : q (modePair γ f) ≤ E) :
    q (spectatorPair β γ f) ≤ 4 * E + 2 * q f := by
  have h := two_spectator_pair_control β γ hβ hγ f
  linarith

theorem spectatorPair_commute (β γ : Orbital ι) (f : Core ι ℂ) :
    spectatorPair β γ f = spectatorPair γ β f :=
  mode_annihilate_commute γ β f

theorem spectatorPair_smul (c d : ℂ) (β γ : Orbital ι) (f : Core ι ℂ) :
    spectatorPair (c • β) (d • γ) f =
      (star d * star c) • spectatorPair β γ f := by
  simp only [spectatorPair, LinearMap.comp_apply, modeAnnihilate_smul,
    LinearMap.smul_apply, map_smul, smul_smul]
  rw [mul_comm (star c) (star d)]

theorem raw_spectator_normSq (c d : ℂ) (β γ : Orbital ι) (f : Core ι ℂ) :
    q (spectatorPair (c • β) (d • γ) f) =
      Complex.normSq c * Complex.normSq d * q (spectatorPair β γ f) := by
  rw [spectatorPair_smul, canonical_normSq_smul]
  simp only [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
  ring

theorem sqrt_raw_spectator_factor (k l : ℝ) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (β γ : Orbital ι) (f : Core ι ℂ) :
    q (spectatorPair ((Real.sqrt k : ℂ) • β) ((Real.sqrt l : ℂ) • γ) f) =
      k * l * q (spectatorPair β γ f) := by
  rw [raw_spectator_normSq, Complex.normSq_ofReal, Complex.normSq_ofReal,
    Real.mul_self_sqrt hk, Real.mul_self_sqrt hl]

theorem sqrt_raw_two_spectator_control (k l : ℝ) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (β γ : Orbital ι) (hβ : ‖β‖ = 1) (hγ : ‖γ‖ = 1) (f : Core ι ℂ) :
    q (spectatorPair ((Real.sqrt k : ℂ) • β) ((Real.sqrt l : ℂ) • γ) f) ≤
      k * l * (2 * q (modePair β f) + 2 * q (modePair γ f) + 2 * q f) := by
  rw [sqrt_raw_spectator_factor k l hk hl]
  exact mul_le_mul_of_nonneg_left (two_spectator_pair_control β γ hβ hγ f)
    (mul_nonneg hk hl)

theorem raw_vector_spectator_factor (u v : Orbital ι) (f : Core ι ℂ) :
    q (spectatorPair u v f) =
      ‖u‖ ^ 2 * ‖v‖ ^ 2 *
        q (spectatorPair (NormedSpace.normalize u) (NormedSpace.normalize v) f) := by
  have h := raw_spectator_normSq (‖u‖ : ℂ) (‖v‖ : ℂ)
    (NormedSpace.normalize u) (NormedSpace.normalize v) f
  rw [raw_vector_expansion, raw_vector_expansion] at h
  simpa only [Complex.normSq_ofReal, pow_two] using h

theorem raw_vector_two_spectator_control (u v : Orbital ι)
    (hu : u ≠ 0) (hv : v ≠ 0) (f : Core ι ℂ) :
    q (spectatorPair u v f) ≤
      ‖u‖ ^ 2 * ‖v‖ ^ 2 *
        (2 * q (modePair (NormedSpace.normalize u) f) +
          2 * q (modePair (NormedSpace.normalize v) f) + 2 * q f) := by
  rw [raw_vector_spectator_factor]
  exact mul_le_mul_of_nonneg_left
    (two_spectator_pair_control _ _ (NormedSpace.norm_normalize hu)
      (NormedSpace.norm_normalize hv) f) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem raw_vector_uniform_spectator_control (s : ℝ) (hs : 0 ≤ s)
    (u v : Orbital ι) (hu : u ≠ 0) (hv : v ≠ 0)
    (huBound : ‖u‖ ^ 2 ≤ s) (hvBound : ‖v‖ ^ 2 ≤ s) (f : Core ι ℂ) :
    q (spectatorPair u v f) ≤
      s ^ 2 * (2 * q (modePair (NormedSpace.normalize u) f) +
        2 * q (modePair (NormedSpace.normalize v) f) + 2 * q f) := by
  have h := raw_vector_two_spectator_control u v hu hv f
  have hprod : ‖u‖ ^ 2 * ‖v‖ ^ 2 ≤ s ^ 2 := by
    simpa only [pow_two] using mul_le_mul huBound hvBound (sq_nonneg ‖v‖) hs
  have hE : 0 ≤ 2 * q (modePair (NormedSpace.normalize u) f) +
      2 * q (modePair (NormedSpace.normalize v) f) + 2 * q f := by
    have ha := occupationMetricNormSq_nonneg (fun _ => 1) (modePair (NormedSpace.normalize u) f)
    have hb := occupationMetricNormSq_nonneg (fun _ => 1) (modePair (NormedSpace.normalize v) f)
    have hc := occupationMetricNormSq_nonneg (fun _ => 1) f
    change 0 ≤ q (modePair (NormedSpace.normalize u) f) at ha
    change 0 ≤ q (modePair (NormedSpace.normalize v) f) at hb
    change 0 ≤ q f at hc
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right hprod hE)

theorem spectatorPair_modePair_commute (β γ δ : Orbital ι) (f : Core ι ℂ) :
    spectatorPair β γ (modePair δ f) = modePair δ (spectatorPair β γ f) := by
  simp only [spectatorPair, modePair, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
  congr 1
  rw [mode_annihilate_commute β δ, mode_annihilate_commute γ δ,
    mode_annihilate_commute β δ, mode_annihilate_commute γ δ]

theorem two_spectator_pair_output_control (β γ δ : Orbital ι)
    (hβ : ‖β‖ = 1) (hγ : ‖γ‖ = 1) (f : Core ι ℂ) :
    q (spectatorPair β γ (modePair δ f)) ≤
      2 * q (modePair β (modePair δ f)) +
        2 * q (modePair γ (modePair δ f)) + 2 * q (modePair δ f) :=
  two_spectator_pair_control β γ hβ hγ (modePair δ f)

theorem spectatorPair_sector (β γ : Orbital ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 2)) : (spectatorPair β γ f).IsHomogeneous N := by
  have h1 : (modeAnnihilate β f).IsHomogeneous (N + 1) :=
    modeAnnihilate_sector β (N + 1) f (by simpa only [Nat.add_assoc] using hf)
  exact modeAnnihilate_sector γ N _ h1

theorem two_spectator_four_body_control (β γ δ : Orbital ι)
    (hβ : ‖β‖ = 1) (hγ : ‖γ‖ = 1) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 4)) :
    (modePair δ f).IsHomogeneous (N + 2) ∧
      (spectatorPair β γ (modePair δ f)).IsHomogeneous N ∧
      (modePair β (modePair δ f)).IsHomogeneous N ∧
      (modePair γ (modePair δ f)).IsHomogeneous N ∧
      q (spectatorPair β γ (modePair δ f)) ≤
        2 * q (modePair β (modePair δ f)) +
          2 * q (modePair γ (modePair δ f)) + 2 * q (modePair δ f) := by
  have hp : (modePair δ f).IsHomogeneous (N + 2) :=
    modePair_sector δ (N + 2) f (by simpa only [Nat.add_assoc] using hf)
  exact ⟨hp, spectatorPair_sector β γ N _ hp, modePair_sector β N _ hp,
    modePair_sector γ N _ hp, two_spectator_pair_output_control β γ δ hβ hγ f⟩

/-- Raw spectators cost s² on the pair-output state. The anchor itself
remains the actual modePair δ, with no extra raw factor appended to it. -/
theorem raw_vector_uniform_pair_output_control (s : ℝ) (hs : 0 ≤ s)
    (u v δ : Orbital ι) (hu : u ≠ 0) (hv : v ≠ 0)
    (huBound : ‖u‖ ^ 2 ≤ s) (hvBound : ‖v‖ ^ 2 ≤ s) (f : Core ι ℂ) :
    q (spectatorPair u v (modePair δ f)) ≤
      s ^ 2 * (2 * q (modePair (NormedSpace.normalize u) (modePair δ f)) +
        2 * q (modePair (NormedSpace.normalize v) (modePair δ f)) + 2 * q (modePair δ f)) :=
  raw_vector_uniform_spectator_control s hs u v hu hv huBound hvBound (modePair δ f)

end
end TorusLean.Boson.SpectatorControl
