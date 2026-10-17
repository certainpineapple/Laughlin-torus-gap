import torus.shared.BosonFiniteCertificateNatComparisonWeights
import torus.shared.BosonFiniteCertificateCanonicalActualComparison303
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
theorem k303_nat_initial_descendant_rename (n : Fin 6) (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))) =
      MvPolynomial.rename Fin.val
        ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n.val] (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))) := by
  fin_cases n
  · rw [c303desc3_actual_Nat, c303desc3_actual]
  · rw [c303desc4_actual_Nat, c303desc4_actual]
  · rw [c303desc5_actual_Nat, c303desc5_actual]
  · rw [c303desc6_actual_Nat, c303desc6_actual]
  · rw [c303desc7_actual_Nat, c303desc7_actual]
  · rw [c303desc8_actual_Nat, c303desc8_actual]

/-- Every term contains the actual natural-label action of all 138 original
rows, the exact pure-pair subtraction, and the displayed COM normalization. -/
theorem k303_nat_finite_COM_form (x y : Fin 1 → ℂ) :
    canonicalNatFiniteCOMForm 3 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ y))) =
      k303actualFiniteCOMForm x y := by
  unfold canonicalNatFiniteCOMForm k303actualFiniteCOMForm
  simp only [k303_nat_initial_descendant_rename, canonicalNatOriginalM3Form_rename]
  exact natCOMComparisonWeight_sum6 (fun n => canonicalOriginalM3Form
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)))
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ y))))

theorem k303_nat_comparison_form (x y : Fin 1 → ℂ) :
    canonicalNatComparisonForm 3 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ y))) =
      k303actualComparisonForm x y := by
  unfold canonicalNatComparisonForm k303actualComparisonForm
  rw [k303_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 3 (by decide) _
      (canonicalBlock_bihomogeneous 3 k303occ k303_particle_degree k303_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9,
    k303_nat_finite_COM_form]

theorem k303_nat_comparison_nonneg (x : Fin 1 → ℂ) :
    0 ≤ (canonicalNatComparisonForm 3 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)))).re := by
  rw [k303_nat_comparison_form]
  exact k303_actual_comparison_nonneg x

/-- No selected-span premise remains: the complete true Nat-lowering kernel
and particle/orbital homogeneity determine the original relative family. -/
theorem k303_nat_homogeneous_comparison_nonneg (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 3)
    (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatComparisonForm 3 f f).re := by
  obtain ⟨x,rfl⟩ := (k303_nat_homogeneous_relative_kernel f hN hd).mp hL
  exact k303_nat_comparison_nonneg x

#print axioms k303_nat_initial_descendant_rename
#print axioms k303_nat_finite_COM_form
#print axioms k303_nat_comparison_form
#print axioms k303_nat_homogeneous_comparison_nonneg
end TorusLean.BosonFiniteCertificate
