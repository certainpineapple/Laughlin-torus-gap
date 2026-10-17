import torus.shared.BosonFiniteCertificateNatComparisonWeights
import torus.shared.BosonFiniteCertificateCanonicalActualComparison300
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
open scoped BigOperators

/-- These initial descendants are genuine unbounded-label iterates; the
finite-operator identity is used only through the already checked endpoints. -/
theorem k300_nat_initial_descendant_rename (n : Fin 9) (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))) =
      MvPolynomial.rename Fin.val
        ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n.val] (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))) := by
  fin_cases n
  · rw [c300desc0_actual_Nat, c300desc0_actual]
  · rw [c300desc1_actual_Nat, c300desc1_actual]
  · rw [c300desc2_actual_Nat, c300desc2_actual]
  · rw [c300desc3_actual_Nat, c300desc3_actual]
  · rw [c300desc4_actual_Nat, c300desc4_actual]
  · rw [c300desc5_actual_Nat, c300desc5_actual]
  · rw [c300desc6_actual_Nat, c300desc6_actual]
  · rw [c300desc7_actual_Nat, c300desc7_actual]
  · rw [c300desc8_actual_Nat, c300desc8_actual]

/-- Every term contains the actual natural-label action of all 138 original
rows, the exact pure-pair subtraction, and the displayed COM normalization. -/
theorem k300_nat_finite_COM_form (x y : Fin 1 → ℂ) :
    canonicalNatFiniteCOMForm 0 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ y))) =
      k300actualFiniteCOMForm x y := by
  unfold canonicalNatFiniteCOMForm k300actualFiniteCOMForm
  simp only [k300_nat_initial_descendant_rename, canonicalNatOriginalM3Form_rename]
  exact natCOMComparisonWeight_sum9 (fun n => canonicalOriginalM3Form
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)))
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ y))))

theorem k300_nat_comparison_form (x y : Fin 1 → ℂ) :
    canonicalNatComparisonForm 0 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ y))) =
      k300actualComparisonForm x y := by
  unfold canonicalNatComparisonForm k300actualComparisonForm
  rw [k300_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 0 (by decide) _
      (canonicalBlock_bihomogeneous 0 k300occ k300_particle_degree k300_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9,
    k300_nat_finite_COM_form]

theorem k300_nat_comparison_nonneg (x : Fin 1 → ℂ) :
    0 ≤ (canonicalNatComparisonForm 0 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)))).re := by
  rw [k300_nat_comparison_form]
  exact k300_actual_comparison_nonneg x

/-- No selected-span premise remains: the complete true Nat-lowering kernel
and particle/orbital homogeneity determine the original relative family. -/
theorem k300_nat_homogeneous_comparison_nonneg (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 0)
    (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatComparisonForm 0 f f).re := by
  obtain ⟨x,rfl⟩ := (k300_nat_homogeneous_relative_kernel f hN hd).mp hL
  exact k300_nat_comparison_nonneg x

#print axioms k300_nat_initial_descendant_rename
#print axioms k300_nat_finite_COM_form
#print axioms k300_nat_comparison_form
#print axioms k300_nat_homogeneous_comparison_nonneg
end TorusLean.BosonFiniteCertificate
