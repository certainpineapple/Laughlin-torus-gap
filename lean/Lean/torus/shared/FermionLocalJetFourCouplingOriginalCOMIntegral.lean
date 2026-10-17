import torus.shared.FermionLocalJetFourCouplingOriginalCOM
import torus.shared.ThermalCoherentFermionAnchoredJacobiRemovalCell

/-! Actual original full-Fock four-body mixed cell integrals.  COM integration
kills unequal relative degrees at fixed T, while every same-degree r,s matrix
unit survives.  The original mu2 measure is unchanged; charge4 contributes
2/4 only in the intermediate mu4 formula. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemovalCell
open TorusLean.Shared.ParameterLadderIntegration
open scoped BigOperators ComplexConjugate

/-- Identification is at the actual exterior multiplication adjoint. -/
theorem sourceRemoval_original_descendant (G : Geometry) (theta : Twist)
    (D T r : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    sourceRemoval (physicalQ G theta) (physicalDescendantColumn G theta D T r R) x =
      descendantFourAmplitude G theta D T r R x := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  exact physicalDescendantColumn_mul_adjoint G theta D T r R y x

/-- Full mixed relative-source identity before converting back to mu2. -/
theorem original_descendant_cell_charge4 (G : Geometry) (theta : Twist)
    (d e : Fin 23) (r : OddMode (d.val+1)) (s : OddMode (e.val+1))
    (n m : ℕ) (hn : d.val+1+n≤23) (hm : e.val+1+m≤23)
    (x y : Space (physicalQ G theta)) :
    (∫ R, occupationInner (physicalQ G theta)
      (descendantFourAmplitude G theta (d.val+1) (d.val+1+n) r.val.val R x)
      (descendantFourAmplitude G theta (e.val+1) (e.val+1+m) s.val.val R y)
        ∂cellMeasure G 2) =
    if n=m then ((2/(4:ℝ):ℝ):ℂ) *
      (∫ R, occupationInner (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x)
        (coupledFourAmplitude G theta (e.val+1) s R y) ∂cellMeasure G 4) else 0 := by
  have h := normalized_removal_same_cell G theta 4
    (highestCoupledWords (d.val+1) r) (highestCoupledWords (e.val+1) s)
    (original_coupled_vacuum d r) (original_coupled_vacuum e s) n m x y
  simp_rw [original_normalized_com_source G theta d r n hn,
    original_normalized_com_source G theta e s m hm,
    sourceRemoval_original_descendant,realize_highestCoupledWords,
    formalRemoval_coupled] at h
  exact h

/-- With the original mu2 measure there is no additional COM factor. -/
theorem original_descendant_same_cell (G : Geometry) (theta : Twist)
    (d e : Fin 23) (r : OddMode (d.val+1)) (s : OddMode (e.val+1))
    (n m : ℕ) (hn : d.val+1+n≤23) (hm : e.val+1+m≤23)
    (x y : Space (physicalQ G theta)) :
    (∫ R, occupationInner (physicalQ G theta)
      (descendantFourAmplitude G theta (d.val+1) (d.val+1+n) r.val.val R x)
      (descendantFourAmplitude G theta (e.val+1) (e.val+1+m) s.val.val R y)
        ∂cellMeasure G 2) =
    if n=m then
      (∫ R, occupationInner (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x)
        (coupledFourAmplitude G theta (e.val+1) s R y) ∂cellMeasure G 2) else 0 := by
  rw [original_descendant_cell_charge4 G theta d e r s n m hn hm x y]
  rw [cellIntegral_two_eq_charge G 4]
  simp only [Nat.cast_ofNat]

/-- At fixed total T only D differs between COM levels. The two copy indices
are arbitrary and independent; this keeps the entire original E_D matrix. -/
theorem original_fullT_mixed_cell (G : Geometry) (theta : Twist)
    (T : Fin 24) (d e : Fin 23) (r : OddMode (d.val+1)) (s : OddMode (e.val+1))
    (hd : d.val+1≤T.val) (he : e.val+1≤T.val)
    (x y : Space (physicalQ G theta)) :
    (∫ R, occupationInner (physicalQ G theta)
      (descendantFourAmplitude G theta (d.val+1) T.val r.val.val R x)
      (descendantFourAmplitude G theta (e.val+1) T.val s.val.val R y)
        ∂cellMeasure G 2) =
    if d=e then
      (∫ R, occupationInner (physicalQ G theta)
        (coupledFourAmplitude G theta (d.val+1) r R x)
        (coupledFourAmplitude G theta (e.val+1) s R y) ∂cellMeasure G 2) else 0 := by
  have hdn : d.val+1+(T.val-(d.val+1))=T.val := Nat.add_sub_of_le hd
  have hen : e.val+1+(T.val-(e.val+1))=T.val := Nat.add_sub_of_le he
  have hiff : T.val-(d.val+1)=T.val-(e.val+1) ↔ d=e := by
    constructor
    · intro h; apply Fin.ext; omega
    · intro h; subst e; rfl
  have h := original_descendant_same_cell G theta d e r s
    (T.val-(d.val+1)) (T.val-(e.val+1)) (by omega) (by omega) x y
  simpa only [hdn,hen,hiff] using h

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.sourceRemoval_original_descendant
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_descendant_cell_charge4
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_descendant_same_cell
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_fullT_mixed_cell
