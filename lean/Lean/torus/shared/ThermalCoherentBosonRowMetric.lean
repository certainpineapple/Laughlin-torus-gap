import torus.shared.ThermalCoherentBosonRowMetricAlgebra
import torus.shared.BosonSystole20Gram

/-! The actual raw-jet Gram error at systole twenty, extended to arbitrary
bosonic finite-core output vectors using their true factorial coefficients.
No annihilator norm estimate or particle-sector bound enters. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowMetric
open TorusLean.Geometry TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetFiniteGram
open TorusLean.Shared.BosonSystole20Gram TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

/-- The actual mixed-jet estimates give the complete complex scalar Gram
bound, including all cross terms and the established common allowance. -/
theorem actual_jetGram_scalar_bound (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D≤16) (R : ℂ) (hG : 20≤systole G) (c : Fin (D+1) → ℂ) :
    ‖∑ i : Fin (D+1), ∑ j : Fin (D+1), conj (c i)*
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R)-if i=j then 1 else 0)*c j‖ ≤
      allowance*∑ i, ‖c i‖^2 := by
  have h := complex_quadratic_norm_le
    (fun i j : Fin (D+1) => inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
      (if i=j then (1:ℂ) else 0)) c (sharpEntryConstant D*8450)
    (mul_nonneg (sharpEntryConstant_nonneg D) (by norm_num)) (by
      intro i j
      have hi : i.val≤D := Nat.le_of_lt_succ i.isLt
      have hj : j.val≤D := Nat.le_of_lt_succ j.isLt
      simpa only [Fin.val_inj] using physical_mixed_gram_error_le G theta D i j hD hi hj R hG)
  calc
    _ ≤ (sharpEntryConstant D*8450*(D+1:ℕ))*∑ i, ‖c i‖^2 := by
      simpa only [Fintype.card_fin] using h
    _ ≤ sharpGramBound D*∑ i, ‖c i‖^2 :=
      mul_le_mul_of_nonneg_right (sharpEntryConstant_mul_card_le D)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((sharpGramBound_le_sixteen D hD).trans sharpGramBound_sixteen_small.le)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Actual complex metric error on arbitrary true bosonic output states. -/
theorem actual_jetGram_occupation_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G : Geometry) (theta : Twist) (D : ℕ) (hD : D≤16) (R : ℂ) (hG : 20≤systole G)
    (Y : Fin (D+1) → Core ι ℂ) :
    ‖∑ i : Fin (D+1), ∑ j : Fin (D+1),
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R)-if i=j then 1 else 0)*
        ip (Y i) (Y j)‖ ≤ allowance*∑ i, q (Y i) :=
  occupation_matrix_bound _ allowance (actual_jetGram_scalar_bound G theta D hD R hG) Y

/-- The two-sided Loewner payment is immediate from the genuine complex bound. -/
theorem actual_jetGram_occupation_real_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G : Geometry) (theta : Twist) (D : ℕ) (hD : D≤16) (R : ℂ) (hG : 20≤systole G)
    (Y : Fin (D+1) → Core ι ℂ) :
    |(∑ i : Fin (D+1), ∑ j : Fin (D+1),
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R)-if i=j then 1 else 0)*
        ip (Y i) (Y j)).re| ≤ allowance*∑ i, q (Y i) :=
  (Complex.abs_re_le_norm _).trans (actual_jetGram_occupation_bound G theta D hD R hG Y)

end TorusLean.Shared.ThermalCoherentBosonRowMetric
