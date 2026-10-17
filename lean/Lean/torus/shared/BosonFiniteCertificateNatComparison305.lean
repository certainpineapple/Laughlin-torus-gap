import torus.shared.BosonFiniteCertificateNatComparisonWeights
import torus.shared.BosonFiniteCertificateCanonicalActualComparison305
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
theorem k305_nat_initial_descendant_rename (n : Fin 4) (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))) =
      MvPolynomial.rename Fin.val
        ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n.val] (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))) := by
  fin_cases n
  · rw [c305desc5_actual_Nat, c305desc5_actual]
  · rw [c305desc6_actual_Nat, c305desc6_actual]
  · rw [c305desc7_actual_Nat, c305desc7_actual]
  · rw [c305desc8_actual_Nat, c305desc8_actual]

/-- Every term contains the actual natural-label action of all 138 original
rows, the exact pure-pair subtraction, and the displayed COM normalization. -/
theorem k305_nat_finite_COM_form (x y : Fin 1 → ℂ) :
    canonicalNatFiniteCOMForm 5 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ y))) =
      k305actualFiniteCOMForm x y := by
  unfold canonicalNatFiniteCOMForm k305actualFiniteCOMForm
  simp only [k305_nat_initial_descendant_rename, canonicalNatOriginalM3Form_rename]
  exact natCOMComparisonWeight_sum4 (fun n => canonicalOriginalM3Form
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)))
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ y))))

theorem k305_nat_comparison_form (x y : Fin 1 → ℂ) :
    canonicalNatComparisonForm 5 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ y))) =
      k305actualComparisonForm x y := by
  unfold canonicalNatComparisonForm k305actualComparisonForm
  rw [k305_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 5 (by decide) _
      (canonicalBlock_bihomogeneous 5 k305occ k305_particle_degree k305_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9,
    k305_nat_finite_COM_form]

theorem k305_nat_comparison_nonneg (x : Fin 1 → ℂ) :
    0 ≤ (canonicalNatComparisonForm 5 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)))).re := by
  rw [k305_nat_comparison_form]
  exact k305_actual_comparison_nonneg x

/-- No selected-span premise remains: the complete true Nat-lowering kernel
and particle/orbital homogeneity determine the original relative family. -/
theorem k305_nat_homogeneous_comparison_nonneg (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 5)
    (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatComparisonForm 5 f f).re := by
  obtain ⟨x,rfl⟩ := (k305_nat_homogeneous_relative_kernel f hN hd).mp hL
  exact k305_nat_comparison_nonneg x

#print axioms k305_nat_initial_descendant_rename
#print axioms k305_nat_finite_COM_form
#print axioms k305_nat_comparison_form
#print axioms k305_nat_homogeneous_comparison_nonneg
end TorusLean.BosonFiniteCertificate
