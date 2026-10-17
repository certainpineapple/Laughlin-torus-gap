import torus.shared.FermionLocalJetFourCouplingDescendants

/-! The actual finite exterior sources of the full-T coupled amplitudes.
These source columns have physical orbital degree T+1. Their expected COM
level is T-D; the raising/parameter and cell-ladder identities are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators ComplexConjugate

def formalDescendantColumn (D T r : ℕ) : FormalExterior :=
  ∑ q : HalfInputIndex T,
    paperS45 r D T q.val.1.val q.val.2.val (T-q.val.1.val-q.val.2.val) •
      (formalPair q.val.1.val * formalJet q.val.2.val * formalJet (T-q.val.1.val-q.val.2.val))

def physicalDescendantColumn (G : Geometry) (theta : Twist) (D T r : ℕ) (R : ℂ) :
    Space (physicalQ G theta) := rawJetExteriorMap G theta R (formalDescendantColumn D T r)

theorem formalDescendantColumn_highest (D : ℕ) (r : OddMode D) :
    formalDescendantColumn D D r.val.val = formalCoupledColumn D r := by
  classical
  unfold formalDescendantColumn
  rw [halfInput_sum D (fun q : InputIndex D =>
    paperS45 r.val.val D D q.1.val q.2.val (D-q.1.val-q.2.val) •
      (formalPair q.1.val * formalJet q.2.val * formalJet (D-q.1.val-q.2.val)))]
  simp only [formalCoupledColumn,Fintype.sum_sigma,maskedS45]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro j hj
  rw [← highestS45_eq_paper D r.val.val (Nat.le_of_lt_succ r.val.isLt)]
  split_ifs <;> simp

private theorem jet_mul_adjoint_full (G : Geometry) (theta : Twist) (R : ℂ) (j : ℕ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (ExteriorAlgebra.ι ℂ (physicalJetCoordinates G theta j R)*x) y =
      occupationInner (physicalQ G theta) x (localJetAnnihilate G theta j R y) :=
  rawCreate_adjoint _ _ _ _

private theorem pair_mul_adjoint_full (G : Geometry) (theta : Twist) (R : ℂ) (p : ℕ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) (rawJetExteriorMap G theta R (formalPair p)*x) y =
      occupationInner (physicalQ G theta) x (pairDescendant G theta p R y) := by
  rw [rawJetExteriorMap_pair,pairDescendant_eq_paper,paperPairDescendant_single_sum]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
    occupationInner_smul_left,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_right,occupationInner_smul_right,Module.End.mul_apply,
    mul_assoc,jet_mul_adjoint_full,Complex.star_def,Complex.conj_ofReal]

/-- True finite exterior map and its original full-Fock CAR occupation adjoint.
There is no orthogonality, isometry, Gram inverse or nonzero-image premise. -/
theorem physicalDescendantColumn_mul_adjoint (G : Geometry) (theta : Twist)
    (D T r : ℕ) (R : ℂ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) (physicalDescendantColumn G theta D T r R*x) y =
      occupationInner (physicalQ G theta) x (descendantFourAmplitude G theta D T r R y) := by
  simp only [physicalDescendantColumn,formalDescendantColumn,map_sum,map_smul,map_mul,
    rawJetExteriorMap_jet,Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
    occupationInner_smul_left,paperS45_star,descendantFourAmplitude,
    occupationInner_sum_right,occupationInner_smul_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_assoc,mul_assoc,pair_mul_adjoint_full,jet_mul_adjoint_full,jet_mul_adjoint_full]
  rfl

theorem physicalDescendantColumn_highest (G : Geometry) (theta : Twist)
    (D : ℕ) (r : OddMode D) (R : ℂ) :
    physicalDescendantColumn G theta D D r.val.val R = physicalCoupledColumn G theta D r R := by
  rw [physicalDescendantColumn,formalDescendantColumn_highest]
  rfl

#print axioms formalDescendantColumn_highest
#print axioms physicalDescendantColumn_mul_adjoint
#print axioms physicalDescendantColumn_highest
end TorusLean.Shared.FermionLocalJet.FourCoupling
