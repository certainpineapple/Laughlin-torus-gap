import torus.shared.BosonFiniteCertificateNatComparisonWeights
import torus.shared.BosonFiniteCertificateCanonicalActualComparison307
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
theorem k307_nat_initial_descendant_rename (n : Fin 2) (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) =
      MvPolynomial.rename Fin.val
        ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n.val] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) := by
  fin_cases n
  · rw [c307desc7_actual_Nat, c307desc7_actual]
  · rw [c307desc8_actual_Nat, c307desc8_actual]

/-- Every term contains the actual natural-label action of all 138 original
rows, the exact pure-pair subtraction, and the displayed COM normalization. -/
theorem k307_nat_finite_COM_form (x y : Fin 1 → ℂ) :
    canonicalNatFiniteCOMForm 7 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))) =
      k307actualFiniteCOMForm x y := by
  unfold canonicalNatFiniteCOMForm k307actualFiniteCOMForm
  simp only [k307_nat_initial_descendant_rename, canonicalNatOriginalM3Form_rename]
  exact natCOMComparisonWeight_sum2 (fun n => canonicalOriginalM3Form
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)))
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))))

theorem k307_nat_comparison_form (x y : Fin 1 → ℂ) :
    canonicalNatComparisonForm 7 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ y))) =
      k307actualComparisonForm x y := by
  unfold canonicalNatComparisonForm k307actualComparisonForm
  rw [k307_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 7 (by decide) _
      (canonicalBlock_bihomogeneous 7 k307occ k307_particle_degree k307_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9,
    k307_nat_finite_COM_form]

theorem k307_nat_comparison_nonneg (x : Fin 1 → ℂ) :
    0 ≤ (canonicalNatComparisonForm 7 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)))).re := by
  rw [k307_nat_comparison_form]
  exact k307_actual_comparison_nonneg x

/-- No selected-span premise remains: the complete true Nat-lowering kernel
and particle/orbital homogeneity determine the original relative family. -/
theorem k307_nat_homogeneous_comparison_nonneg (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 7)
    (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatComparisonForm 7 f f).re := by
  obtain ⟨x,rfl⟩ := (k307_nat_homogeneous_relative_kernel f hN hd).mp hL
  exact k307_nat_comparison_nonneg x

#print axioms k307_nat_initial_descendant_rename
#print axioms k307_nat_finite_COM_form
#print axioms k307_nat_comparison_form
#print axioms k307_nat_homogeneous_comparison_nonneg
end TorusLean.BosonFiniteCertificate
