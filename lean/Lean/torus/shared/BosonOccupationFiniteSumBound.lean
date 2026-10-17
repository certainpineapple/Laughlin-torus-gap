import torus.shared.BosonModeOccupationBounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Polynomial rather than exponential growth for finite sums of actual
occupation vectors. The seminorm used locally is proved from the unchanged
occupation form and introduces no completion or bounded full-Fock operators. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonOccupationFiniteSumBound
open TorusLean.Boson
open scoped BigOperators ComplexConjugate
variable {ι I : Type*} [Fintype ι]

/-- Finite occupation Cauchy--Schwarz; zero scales and the empty sum are included. -/
theorem occupationMetricNormSq_sum_le (scale : ι → ℕ) (s : Finset I)
    (f : I → Core ι ℂ) :
    occupationMetricNormSq scale (∑ i ∈ s, f i) ≤
      (s.card : ℝ) * ∑ i ∈ s, occupationMetricNormSq scale (f i) := by
  letI : PreInnerProductSpace.Core ℂ (Core ι ℂ) := {
    inner := occupationInner scale
    conj_inner_symm := fun f g => occupationInner_conj_symm scale g f
    re_inner_nonneg := occupationInner_self_nonneg scale
    add_left := occupationInner_add_left scale
    smul_left := fun f g c => occupationInner_smul_left scale c f g }
  letI := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := Core ι ℂ)
  have hn (p : Core ι ℂ) : ‖p‖ ^ 2 = occupationMetricNormSq scale p := by
    change (Real.sqrt (occupationInner scale p p).re)^2 = _
    rw [occupationInner_self_re, Real.sq_sqrt (occupationMetricNormSq_nonneg scale p)]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hfinal := h.trans hc
  simpa only [hn] using hfinal

/-- Three actual moving removals, with a fixed-N polynomial domain bound.
The deliberately loose cubic constant is not a same-H payment estimate. -/
theorem modeAnnihilate_triple_normSq_le [DecidableEq ι]
    (u v w : TorusLean.Boson.UnitaryTransport.Orbital ι)
    (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous (N+3)) :
    occupationMetricNormSq (fun _ => 1)
      (TorusLean.Boson.UnitaryTransport.modeAnnihilate w
        (TorusLean.Boson.UnitaryTransport.modeAnnihilate v
          (TorusLean.Boson.UnitaryTransport.modeAnnihilate u f))) ≤
      ((N:ℝ)+3)^3 * ‖u‖^2 * ‖v‖^2 * ‖w‖^2 *
        occupationMetricNormSq (fun _ => 1) f := by
  let a := TorusLean.Boson.UnitaryTransport.modeAnnihilate u f
  let b := TorusLean.Boson.UnitaryTransport.modeAnnihilate v a
  have ha : a.IsHomogeneous (N+2) :=
    TorusLean.Boson.UnitaryTransport.modeAnnihilate_sector u (N+2) f (by
      simpa only [Nat.add_assoc] using hf)
  have hb : b.IsHomogeneous (N+1) :=
    TorusLean.Boson.UnitaryTransport.modeAnnihilate_sector v (N+1) a (by
      simpa only [Nat.add_assoc] using ha)
  have h1 := BosonModeOccupationBounds.modeAnnihilate_normSq_le u (N+3) f hf
  have h2 := BosonModeOccupationBounds.modeAnnihilate_normSq_le v (N+2) a ha
  have h3 := BosonModeOccupationBounds.modeAnnihilate_normSq_le w (N+1) b hb
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h1 h2 h3
  have h2' : occupationMetricNormSq (fun _ => 1) b ≤
      ((N:ℝ)+3)*‖v‖^2*occupationMetricNormSq (fun _ => 1) a := by
    dsimp [b]
    nlinarith [mul_nonneg (sq_nonneg ‖v‖) (occupationMetricNormSq_nonneg (fun _ => 1) a)]
  have h3' : occupationMetricNormSq (fun _ => 1)
      (TorusLean.Boson.UnitaryTransport.modeAnnihilate w b) ≤
      ((N:ℝ)+3)*‖w‖^2*occupationMetricNormSq (fun _ => 1) b := by
    nlinarith [mul_nonneg (sq_nonneg ‖w‖) (occupationMetricNormSq_nonneg (fun _ => 1) b)]
  calc
    _ ≤ ((N:ℝ)+3)*‖w‖^2*occupationMetricNormSq (fun _ => 1) b := h3'
    _ ≤ ((N:ℝ)+3)*‖w‖^2*
        (((N:ℝ)+3)*‖v‖^2*occupationMetricNormSq (fun _ => 1) a) :=
      mul_le_mul_of_nonneg_left h2' (by positivity)
    _ ≤ ((N:ℝ)+3)*‖w‖^2*
        (((N:ℝ)+3)*‖v‖^2*(((N:ℝ)+3)*‖u‖^2*occupationMetricNormSq (fun _ => 1) f)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
    _ = _ := by ring

#print axioms occupationMetricNormSq_sum_le
#print axioms modeAnnihilate_triple_normSq_le
end TorusLean.Shared.BosonOccupationFiniteSumBound
