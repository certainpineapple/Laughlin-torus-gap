import torus.shared.BosonFiniteCertificateNatComparisonWeights
import torus.shared.BosonFiniteCertificateCanonicalActualComparison306
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
theorem k306_nat_initial_descendant_rename (n : Fin 3) (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n.val] (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) =
      MvPolynomial.rename Fin.val
        ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n.val] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) := by
  fin_cases n
  · rw [c306desc6_actual_Nat, c306desc6_actual]
  · rw [c306desc7_actual_Nat, c306desc7_actual]
  · rw [c306desc8_actual_Nat, c306desc8_actual]

/-- Every term contains the actual natural-label action of all 138 original
rows, the exact pure-pair subtraction, and the displayed COM normalization. -/
theorem k306_nat_finite_COM_form (x y : Fin 2 → ℂ) :
    canonicalNatFiniteCOMForm 6 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) =
      k306actualFiniteCOMForm x y := by
  unfold canonicalNatFiniteCOMForm k306actualFiniteCOMForm
  simp only [k306_nat_initial_descendant_rename, canonicalNatOriginalM3Form_rename]
  exact natCOMComparisonWeight_sum3 (fun n => canonicalOriginalM3Form
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)))
    ((canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[n] (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))))

theorem k306_nat_comparison_form (x y : Fin 2 → ℂ) :
    canonicalNatComparisonForm 6 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ y))) =
      k306actualComparisonForm x y := by
  unfold canonicalNatComparisonForm k306actualComparisonForm
  rw [k306_nat_pair_square_rename,
    canonicalPairHamiltonianNat_rename_low_degree 6 (by decide) _
      (canonicalBlock_bihomogeneous 6 k306occ k306_particle_degree k306_orbital_degree _).2,
    natOccupationInner_rename_fin9,natOccupationInner_rename_fin9,
    k306_nat_finite_COM_form]

theorem k306_nat_comparison_nonneg (x : Fin 2 → ℂ) :
    0 ≤ (canonicalNatComparisonForm 6 (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x))) (MvPolynomial.rename Fin.val (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)))).re := by
  rw [k306_nat_comparison_form]
  exact k306_actual_comparison_nonneg x

/-- No selected-span premise remains: the complete true Nat-lowering kernel
and particle/orbital homogeneity determine the original relative family. -/
theorem k306_nat_homogeneous_comparison_nonneg (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 6)
    (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatComparisonForm 6 f f).re := by
  obtain ⟨x,rfl⟩ := (k306_nat_homogeneous_relative_kernel f hN hd).mp hL
  exact k306_nat_comparison_nonneg x

#print axioms k306_nat_initial_descendant_rename
#print axioms k306_nat_finite_COM_form
#print axioms k306_nat_comparison_form
#print axioms k306_nat_homogeneous_comparison_nonneg
end TorusLean.BosonFiniteCertificate
