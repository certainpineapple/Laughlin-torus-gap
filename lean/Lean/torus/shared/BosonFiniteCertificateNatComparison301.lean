import torus.shared.BosonFiniteCertificateNatComparisonWeights
import torus.shared.BosonFiniteCertificateCanonicalActualComparison301
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
theorem k301_nat_initial_descendant_rename (n : Fin 8) (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) =
      MvPolynomial.rename Fin.val
        ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n.val] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) := by
  fin_cases n
  · rw [c301desc1_actual_Nat, c301desc1_actual]
  · rw [c301desc2_actual_Nat, c301desc2_actual]
  · rw [c301desc3_actual_Nat, c301desc3_actual]
  · rw [c301desc4_actual_Nat, c301desc4_actual]
  · rw [c301desc5_actual_Nat, c301desc5_actual]
  · rw [c301desc6_actual_Nat, c301desc6_actual]
  · rw [c301desc7_actual_Nat, c301desc7_actual]
  · rw [c301desc8_actual_Nat, c301desc8_actual]

/-- Every term contains the actual natural-label action of all 138 original
rows, the exact pure-pair subtraction, and the displayed COM normalization. -/
theorem k301_nat_finite_COM_form (x y : Fin 0 → ℂ) :
    canonicalNatFiniteCOMForm 1 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      k301actualFiniteCOMForm x y := by
  unfold canonicalNatFiniteCOMForm k301actualFiniteCOMForm
  simp only [k301_nat_initial_descendant_rename, canonicalNatOriginalM3Form_rename]
  exact natCOMComparisonWeight_sum8 (fun n => canonicalOriginalM3Form
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)))
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))))

theorem k301_nat_comparison_form (x y : Fin 0 → ℂ) :
    canonicalNatComparisonForm 1 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ y))) =
      k301actualComparisonForm x y := by
  unfold canonicalNatComparisonForm k301actualComparisonForm
  rw [k301_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 1 (by decide) _
      (canonicalBlock_bihomogeneous 1 k301occ k301_particle_degree k301_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9,
    k301_nat_finite_COM_form]

theorem k301_nat_comparison_nonneg (x : Fin 0 → ℂ) :
    0 ≤ (canonicalNatComparisonForm 1 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)))).re := by
  rw [k301_nat_comparison_form]
  exact k301_actual_comparison_nonneg x

/-- No selected-span premise remains: the complete true Nat-lowering kernel
and particle/orbital homogeneity determine the original relative family. -/
theorem k301_nat_homogeneous_comparison_nonneg (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 1)
    (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatComparisonForm 1 f f).re := by
  obtain ⟨x,rfl⟩ := (k301_nat_homogeneous_relative_kernel f hN hd).mp hL
  exact k301_nat_comparison_nonneg x

#print axioms k301_nat_initial_descendant_rename
#print axioms k301_nat_finite_COM_form
#print axioms k301_nat_comparison_form
#print axioms k301_nat_homogeneous_comparison_nonneg
end TorusLean.BosonFiniteCertificate
