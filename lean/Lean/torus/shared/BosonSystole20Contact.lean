import torus.shared.BosonSystole20Gram
import torus.shared.PhysicalBosonPairBudget

/-! Systole-twenty numerical consequences for the existing physical
charge-one/two evaluation maps and unchanged all-N pair contact form.
This does not assert pair almost-idempotence or a four-body frame bound. -/
set_option autoImplicit false
set_option exponentiation.threshold 1000
noncomputable section

namespace TorusLean.Shared.BosonSystole20Contact

open MeasureTheory
open TorusLean.Fermion.LatticePacking
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Shared.BosonSystole20Gram
open TorusLean.Shared.ChargeTwoEvaluation TorusLean.Shared.PlaneJetGramBounds
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonFullContact
open TorusLean.Shared.PhysicalBosonPairBudget

private theorem gaussian_at_fifty_small : Real.exp (-50 : ℝ) * gaussianConstant ≤ allowance := by
  have he : Real.exp (-50 : ℝ) ≤ 1 / (2 : ℝ)^72 := by
    convert (exp_neg_nat_mul_bound 72 (by decide)).le using 1; norm_num
  calc
    _ ≤ (1 / (2 : ℝ)^72) * 8450 :=
      mul_le_mul he gaussianConstant_le gaussianConstant_nonneg (by positivity)
    _ ≤ _ := by norm_num [allowance]

private theorem gaussian_at_hundred_small : Real.exp (-100 : ℝ) * gaussianConstant ≤ allowance := by
  calc
    _ ≤ (1 / (2 : ℝ)^144) * 8450 :=
      mul_le_mul exp_neg_onehundred.le gaussianConstant_le gaussianConstant_nonneg (by positivity)
    _ ≤ _ := by norm_num [allowance]

/-- Actual charge-one density is close to one, uniformly in center and twist. -/
theorem evaluation_one_density_error (G : Geometry) (theta : Twist)
    (R : ℂ) (hL : 20 ≤ systole G) :
    |‖lllEvaluation G theta 1 R‖^2 - 1| ≤ allowance := by
  rw [evaluation_one_norm]
  have h := rawPlaneJet_norm_sq_sub_one_le G theta 0 R 20 (by norm_num) hL (by norm_num)
  norm_num only [show (-(20 : ℝ)^2/8) = -50 by norm_num] at h
  exact h.trans gaussian_at_fifty_small

/-- Actual charge-two density, including the accepted charge-scaling isometry. -/
theorem evaluation_two_density_error (G : Geometry) (theta : Twist)
    (R : ℂ) (hL : 20 ≤ systole G) :
    |‖lllEvaluation G theta 2 R‖^2 - 1| ≤ allowance := by
  have h := evaluation_two_norm_sq_sub_one_le G theta R 20 (by norm_num) hL
  norm_num only [show (-(20 : ℝ)^2/4) = -100 by norm_num] at h
  exact h.trans gaussian_at_hundred_small

theorem evaluation_one_density_pos (G : Geometry) (theta : Twist)
    (R : ℂ) (hL : 20 ≤ systole G) : 0 < ‖lllEvaluation G theta 1 R‖^2 := by
  have h := (abs_le.mp (evaluation_one_density_error G theta R hL)).1
  norm_num [allowance] at h
  linarith

theorem evaluation_one_density_le (G : Geometry) (theta : Twist)
    (R : ℂ) (hL : 20 ≤ systole G) : ‖lllEvaluation G theta 1 R‖^2 ≤ sAllowance := by
  have h := (abs_le.mp (evaluation_one_density_error G theta R hL)).2
  unfold sAllowance
  linarith

/-- The physically required denominator is the SQUARE of the charge-one
norm squared, not its first power. Positivity is proved, not postulated. -/
theorem evaluation_density_ratio_le (G : Geometry) (theta : Twist)
    (R : ℂ) (hL : 20 ≤ systole G) :
    ‖lllEvaluation G theta 2 R‖^2 / (‖lllEvaluation G theta 1 R‖^2)^2 ≤ cAllowance := by
  have h1 := (abs_le.mp (evaluation_one_density_error G theta R hL)).1
  have h2 := (abs_le.mp (evaluation_two_density_error G theta R hL)).2
  have hlow : 1-allowance ≤ ‖lllEvaluation G theta 1 R‖^2 := by linarith
  have hsq : (1-allowance)^2 ≤ (‖lllEvaluation G theta 1 R‖^2)^2 := by
    exact pow_le_pow_left₀ (by norm_num [allowance]) hlow 2
  calc
    _ ≤ (1+allowance) / (‖lllEvaluation G theta 1 R‖^2)^2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ ≤ (1+allowance) / (1-allowance)^2 :=
      div_le_div_of_nonneg_left (by norm_num [allowance]) (by norm_num [allowance]) hsq
    _ = cAllowance := rfl

/-- No N factor or identity-operator payment: the fixed allowance multiplies
exactly the already established actual physical contact energy. -/
theorem physical_pair_budget_twenty (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2)) (hL : 20 ≤ systole G) :
    (∫ z, ‖physicalPairFunction G theta N R f z‖^2 ∂sectorMeasure G N) ≤
      (1+allowance) * actualParticleContactEnergy G (N+2) f.val := by
  apply (physicalPairFunction_geometric_bound G theta N R f 20 (by norm_num) hL).trans
  have hE : 0 ≤ actualParticleContactEnergy G (N+2) f.val := by
    rw [fullCarrier_contact_energy_same_lift]
    exact TorusLean.Boson.PhysicalContactLiftCandidate.contactCoreHamiltonian_nonneg G theta _
  apply mul_le_mul_of_nonneg_right _ hE
  norm_num only [show (-(20 : ℝ)^2/4) = -100 by norm_num]
  linarith [gaussian_at_hundred_small]

#print axioms evaluation_one_density_error
#print axioms evaluation_two_density_error
#print axioms evaluation_one_density_pos
#print axioms evaluation_one_density_le
#print axioms evaluation_density_ratio_le
#print axioms physical_pair_budget_twenty

end TorusLean.Shared.BosonSystole20Contact
