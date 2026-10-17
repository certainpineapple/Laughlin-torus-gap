import UnitaryTransport
import torus.shared.BosonOccupationCrossBound

/-! Fixed-particle-number estimates for genuine moving creation/removal modes.
These bounds are for domain and convergence arguments only. Their N-dependent
constants do not replace the particle-independent same-H occupation payment. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonModeOccupationBounds
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.BosonBridge.OccupationInstance
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate removal is bounded on its true N-particle homogeneous sector. -/
theorem annihilate_normSq_le (i : ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) :
    occupationMetricNormSq (fun _ => 1) (annihilate i f) ≤
      (N : ℝ) * occupationMetricNormSq (fun _ => 1) f := by
  classical
  rw [unit_annihilation_form (fun _ => 1) i rfl,
    occupationMoment_eq_finite, occupationMetricNormSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hni : n i ≤ N := by
    have hw := hf (MvPolynomial.mem_support_iff.mp hn)
    exact (Finsupp.le_weight (1 : ι → ℕ) (by simp : (1 : ι → ℕ) i ≠ 0) n).trans_eq hw
  have h := mul_le_mul_of_nonneg_left (show (n i : ℝ) ≤ (N : ℝ) by exact_mod_cast hni)
    (mul_nonneg (Nat.cast_nonneg (occupationMetricWeight (fun _ => 1) n))
      (Complex.normSq_nonneg (f.coeff n)))
  simpa only [mul_comm (N : ℝ)] using h

/-- Actual second quantization transfers the coordinate estimate to any unit
column, retaining the true homogeneous-sector premise. -/
theorem unitary_column_annihilate_normSq_le (U : Unitary ι) (i : ι)
    (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    occupationMetricNormSq (fun _ => 1)
      (modeAnnihilate (U (EuclideanSpace.single i 1)) f) ≤
        (N : ℝ) * occupationMetricNormSq (fun _ => 1) f := by
  let g := secondQuantization U.symm f
  have hg : g.IsHomogeneous N := secondQuantization_sector U.symm N f hf
  have he : secondQuantization U g = f := secondQuantization_inverse U f
  have h := annihilate_normSq_le i N g hg
  rw [← secondQuantization_normSq U (annihilate i g),
    ← secondQuantization_normSq U g, ← secondQuantization_annihilate, he] at h
  exact h

/-- Unit moving modes, with no orthogonality or chosen-basis hypothesis. -/
theorem normalized_mode_annihilate_normSq_le [Nonempty ι]
    (u : Orbital ι) (hu : ‖u‖ = 1) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate u f) ≤
      (N : ℝ) * occupationMetricNormSq (fun _ => 1) f := by
  obtain ⟨U,hU⟩ := exists_unitary_maps_single (Classical.arbitrary ι) u hu
  simpa only [hU] using unitary_column_annihilate_normSq_le U (Classical.arbitrary ι) N f hf

/-- The general raw moving mode, including zero modes and an empty mode set. -/
theorem modeAnnihilate_normSq_le (u : Orbital ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate u f) ≤
      (N : ℝ) * ‖u‖ ^ 2 * occupationMetricNormSq (fun _ => 1) f := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    simp [modeAnnihilate, occupationMetricNormSq, show u = 0 from Subsingleton.elim _ _]
  | inr h =>
    letI := h
    by_cases hu : u = 0
    · subst u
      simp [modeAnnihilate, occupationMetricNormSq]
    · rw [(raw_vector_factors u f).1]
      have h := mul_le_mul_of_nonneg_left
        (normalized_mode_annihilate_normSq_le (NormedSpace.normalize u)
          (NormedSpace.norm_normalize hu) N f hf) (sq_nonneg ‖u‖)
      simpa only [mul_left_comm, mul_assoc] using h

/-- Exact CCR norm identity on every polynomial, without a degree assumption. -/
theorem modeCreate_normSq (u : Orbital ι) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeCreate u f) =
      occupationMetricNormSq (fun _ => 1) (modeAnnihilate u f) +
        ‖u‖ ^ 2 * occupationMetricNormSq (fun _ => 1) f := by
  have ha : occupationInner (fun _ => 1) f (modeCreate u (modeAnnihilate u f)) =
      occupationInner (fun _ => 1) (modeAnnihilate u f) (modeAnnihilate u f) := by
    have h := congrArg star (mode_create_adjoint u (modeAnnihilate u f) f)
    simpa only [occupationInner_conj_symm] using h
  have h : occupationInner (fun _ => 1) (modeCreate u f) (modeCreate u f) =
      occupationInner (fun _ => 1) (modeAnnihilate u f) (modeAnnihilate u f) +
        inner ℂ u u * occupationInner (fun _ => 1) f f := by
    rw [mode_create_adjoint, mode_mixed_ccr, occupationInner_add_right,
      occupationInner_smul_right, ha]
  simp only [occupationInner_self, inner_self_eq_norm_sq_to_K] at h
  change (occupationMetricNormSq (fun _ => 1) (modeCreate u f) : ℂ) =
    (occupationMetricNormSq (fun _ => 1) (modeAnnihilate u f) : ℂ) +
      (‖u‖ : ℂ) ^ 2 * (occupationMetricNormSq (fun _ => 1) f : ℂ) at h
  exact_mod_cast h

/-- Raw creation on the genuine N-particle sector. -/
theorem modeCreate_normSq_le (u : Orbital ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) :
    occupationMetricNormSq (fun _ => 1) (modeCreate u f) ≤
      ((N : ℝ) + 1) * ‖u‖ ^ 2 * occupationMetricNormSq (fun _ => 1) f := by
  rw [modeCreate_normSq]
  have h := modeAnnihilate_normSq_le u N f hf
  nlinarith

#print axioms annihilate_normSq_le
#print axioms unitary_column_annihilate_normSq_le
#print axioms normalized_mode_annihilate_normSq_le
#print axioms modeAnnihilate_normSq_le
#print axioms modeCreate_normSq
#print axioms modeCreate_normSq_le
end TorusLean.Shared.BosonModeOccupationBounds
