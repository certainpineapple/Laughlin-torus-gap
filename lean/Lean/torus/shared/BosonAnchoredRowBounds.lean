import torus.shared.BosonAnchoredPairRows
import torus.shared.BosonOccupationFiniteSumBound
import torus.shared.PlaneJetGramBounds

/-! Genuine physical anchored rows have polynomial degree growth at each
fixed input particle number. The original raw jets and cell basis are retained.
These estimates supply absolute-convergence domination, not same-H payment. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredRowBounds
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.BosonBridge.OccupationInstance
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonAnchoredTripleRows
open TorusLean.Shared.BosonAnchoredPairRows TorusLean.Shared.BosonPairCOMCoefficientBound
open TorusLean.Shared.BosonOccupationFiniteSumBound
open TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentSpectralOccupation
open TorusLean.Shared.PlaneJetGramBounds TorusLean.Shared.PlaneJetMembership
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate
local instance rowBounds_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private theorem real_smul_normSq_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ℝ) (hc : |c| ≤ 1) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) ((c:ℂ) • f) ≤
      occupationMetricNormSq (fun _ => 1) f := by
  rw [metricNormSq_smul (fun _ => 1) _ _ (Classical.arbitrary ι)]
  have hs : Complex.normSq (c:ℂ) ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg c) hc 2
    rw [sq_abs, one_pow] at h
    simpa only [Complex.normSq_ofReal, pow_two] using h
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs
    (occupationMetricNormSq_nonneg (fun _ => 1) f)

/-- The one-particle bound is transported by the actual cell orthonormal basis. -/
theorem rawJetMode_norm_sq_le (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (j : ℕ) (R : ℂ) :
    ‖rawJetMode G theta j R‖^2 ≤ (4096+gaussianConstant)*(1+(j:ℝ)) := by
  simpa only [rawJetMode, LinearIsometryEquiv.norm_map] using
    rawPlaneJet_norm_sq_le G theta hG j R

/-- The original second anchored column, under a common raw-mode budget. -/
theorem pairAnchored_row_normSq_le (G : Geometry) (theta : Twist) (R : ℂ)
    (l N : ℕ) (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous (N+3))
    (B : ℝ) (hB : 0 ≤ B) (hm : ∀ i ≤ l, ‖rawJetMode G theta i R‖^2 ≤ B) :
    occupationMetricNormSq (fun _ => 1)
      (natThreeAnnihilator G theta R (pairAnchoredSeed l) f) ≤
      ((l:ℝ)+1)^2 * ((N:ℝ)+3)^3 * B^3 * occupationMetricNormSq (fun _ => 1) f := by
  classical
  let T := ((N:ℝ)+3)^3 * B^3 * occupationMetricNormSq (fun _ => 1) f
  have hq := occupationMetricNormSq_nonneg (fun _ => 1) f
  have ht (i : ℕ) (hi : i ∈ Finset.range (l+1)) :
      occupationMetricNormSq (fun _ => 1) ((pairCOMCoefficientReal l i : ℂ) •
        modeAnnihilate (rawJetMode G theta 0 R)
          (modeAnnihilate (rawJetMode G theta (l-i) R)
            (modeAnnihilate (rawJetMode G theta i R) f))) ≤ T := by
    have hil : i ≤ l := by have := Finset.mem_range.mp hi; omega
    apply (real_smul_normSq_le _ (pairCOMCoefficientReal_abs_le_one l i hil) _).trans
    apply (modeAnnihilate_triple_normSq_le (rawJetMode G theta i R)
      (rawJetMode G theta (l-i) R) (rawJetMode G theta 0 R) N f hf).trans
    calc
      _ ≤ ((N:ℝ)+3)^3 * B * B * B * occupationMetricNormSq (fun _ => 1) f := by
        gcongr
        · exact hm i hil
        · exact hm (l-i) (Nat.sub_le _ _)
        · exact hm 0 (Nat.zero_le _)
      _ = T := by dsimp [T]; ring
  rw [pairAnchoredSeed_row_expansion]
  apply (occupationMetricNormSq_sum_le (fun _ => 1) (Finset.range (l+1)) _).trans
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum ht)
    (show 0 ≤ ((Finset.range (l+1)).card:ℝ) by positivity)
  calc
    _ ≤ ((Finset.range (l+1)).card:ℝ) * ∑ _i ∈ Finset.range (l+1), T := hs
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
                  Nat.cast_one]; dsimp [T]; ring

/-- Uniform-in-center degree-five growth for the actual pair-COM anchored row. -/
theorem pairAnchored_row_normSq_polynomial (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (R : ℂ) (l N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous (N+3)) :
    occupationMetricNormSq (fun _ => 1)
      (natThreeAnnihilator G theta R (pairAnchoredSeed l) f) ≤
      (4096+gaussianConstant)^3 * ((N:ℝ)+3)^3 * ((l:ℝ)+1)^5 *
        occupationMetricNormSq (fun _ => 1) f := by
  have hC : 0 ≤ 4096+gaussianConstant := by linarith [gaussianConstant_nonneg]
  have h := pairAnchored_row_normSq_le G theta R l N f hf
    ((4096+gaussianConstant)*((l:ℝ)+1)) (by positivity) (by
      intro i hi
      apply (rawJetMode_norm_sq_le G theta hG i R).trans
      have hcast : (i:ℝ) ≤ l := by exact_mod_cast hi
      nlinarith)
  convert h using 1 <;> ring

/-- The original first anchored column, under the same common raw-mode budget. -/
theorem w3_row_normSq_le (G : Geometry) (theta : Twist) (R : ℂ)
    (l N : ℕ) (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous (N+3))
    (B : ℝ) (hB : 0 ≤ B) (hm : ∀ i ≤ l, ‖rawJetMode G theta i R‖^2 ≤ B) :
    occupationMetricNormSq (fun _ => 1)
      (natThreeAnnihilator G theta R (w3Seed l) f) ≤
      ((N:ℝ)+3)^3 * B^3 * occupationMetricNormSq (fun _ => 1) f := by
  have hreal : star ((Real.sqrt (2:ℝ):ℂ)⁻¹) = (Real.sqrt (2:ℝ):ℂ)⁻¹ := by simp
  have he : natThreeAnnihilator G theta R (w3Seed l) f =
      (((Real.sqrt (2:ℝ))⁻¹ : ℝ):ℂ) •
        modeAnnihilate (rawJetMode G theta l R)
          (modeAnnihilate (rawJetMode G theta 0 R)
            (modeAnnihilate (rawJetMode G theta 0 R) f)) := by
    simp only [w3Seed, pairVacuum, pow_two, smul_mul_assoc, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, starRingEnd_apply,
      Complex.ofReal_inv, natThreeAnnihilator_triple]
    rw [hreal]
  rw [he]
  have hs : |(Real.sqrt (2:ℝ))⁻¹| ≤ 1 := by
    have hp := Real.sqrt_nonneg (2:ℝ)
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hroot : 1 ≤ Real.sqrt (2:ℝ) := by nlinarith
    rw [abs_of_nonneg (inv_nonneg.mpr hp)]
    exact inv_le_one_of_one_le₀ hroot
  apply (real_smul_normSq_le _ hs _).trans
  apply (modeAnnihilate_triple_normSq_le (rawJetMode G theta 0 R)
    (rawJetMode G theta 0 R) (rawJetMode G theta l R) N f hf).trans
  have hq := occupationMetricNormSq_nonneg (fun _ => 1) f
  calc
    _ ≤ ((N:ℝ)+3)^3 * B * B * B * occupationMetricNormSq (fun _ => 1) f := by
      gcongr
      · exact hm 0 (Nat.zero_le _)
      · exact hm 0 (Nat.zero_le _)
      · exact hm l le_rfl
    _ = _ := by ring

/-- Uniform-in-center cubic degree growth for the original pair-plus-spectator row. -/
theorem w3_row_normSq_polynomial (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (R : ℂ) (l N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous (N+3)) :
    occupationMetricNormSq (fun _ => 1)
      (natThreeAnnihilator G theta R (w3Seed l) f) ≤
      (4096+gaussianConstant)^3 * ((N:ℝ)+3)^3 * ((l:ℝ)+1)^3 *
        occupationMetricNormSq (fun _ => 1) f := by
  have hC : 0 ≤ 4096+gaussianConstant := by linarith [gaussianConstant_nonneg]
  have h := w3_row_normSq_le G theta R l N f hf
    ((4096+gaussianConstant)*((l:ℝ)+1)) (by positivity) (by
      intro i hi
      apply (rawJetMode_norm_sq_le G theta hG i R).trans
      have hcast : (i:ℝ) ≤ l := by exact_mod_cast hi
      nlinarith)
  convert h using 1 <;> ring

#print axioms rawJetMode_norm_sq_le
#print axioms pairAnchored_row_normSq_le
#print axioms pairAnchored_row_normSq_polynomial
#print axioms w3_row_normSq_le
#print axioms w3_row_normSq_polynomial
end TorusLean.Shared.BosonAnchoredRowBounds
