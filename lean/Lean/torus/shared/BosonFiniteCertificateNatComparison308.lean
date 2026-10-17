import torus.shared.BosonFiniteCertificateNatComparisonWeights
import torus.shared.BosonFiniteCertificateCanonicalActualComparison308
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
theorem k308_nat_initial_descendant_rename (n : Fin 1) (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) =
      MvPolynomial.rename Fin.val
        ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n.val] (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) := by
  fin_cases n
  · rw [c308desc8_actual_Nat, c308desc8_actual]

/-- Every term contains the actual natural-label action of all 138 original
rows, the exact pure-pair subtraction, and the displayed COM normalization. -/
theorem k308_nat_finite_COM_form (x y : Fin 2 → ℂ) :
    canonicalNatFiniteCOMForm 8 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y))) =
      k308actualFiniteCOMForm x y := by
  unfold canonicalNatFiniteCOMForm k308actualFiniteCOMForm
  simp only [k308_nat_initial_descendant_rename, canonicalNatOriginalM3Form_rename]
  exact natCOMComparisonWeight_sum1 (fun n => canonicalOriginalM3Form
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)))
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y))))

theorem k308_nat_comparison_form (x y : Fin 2 → ℂ) :
    canonicalNatComparisonForm 8 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ y))) =
      k308actualComparisonForm x y := by
  unfold canonicalNatComparisonForm k308actualComparisonForm
  rw [k308_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 8 (by decide) _
      (canonicalBlock_bihomogeneous 8 k308occ k308_particle_degree k308_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9,
    k308_nat_finite_COM_form]

theorem k308_nat_comparison_nonneg (x : Fin 2 → ℂ) :
    0 ≤ (canonicalNatComparisonForm 8 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)))).re := by
  rw [k308_nat_comparison_form]
  exact k308_actual_comparison_nonneg x

/-- No selected-span premise remains: the complete true Nat-lowering kernel
and particle/orbital homogeneity determine the original relative family. -/
theorem k308_nat_homogeneous_comparison_nonneg (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 8)
    (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatComparisonForm 8 f f).re := by
  obtain ⟨x,rfl⟩ := (k308_nat_homogeneous_relative_kernel f hN hd).mp hL
  exact k308_nat_comparison_nonneg x

#print axioms k308_nat_initial_descendant_rename
#print axioms k308_nat_finite_COM_form
#print axioms k308_nat_comparison_form
#print axioms k308_nat_homogeneous_comparison_nonneg
end TorusLean.BosonFiniteCertificate
