import torus.shared.FermionLocalJetFourCouplingPhysical
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-! The manuscript highest-weight four-form itself, not just its coefficient
array. The formal raw modes are sent by the actual C_R to torus jet coordinates.
The resulting exterior four-form's left multiplication has exactly the coupled
CAR amplitude as occupation adjoint, including all annihilation order and signs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators ComplexConjugate

abbrev FormalOrbital := ℕ →₀ ℂ
abbrev FormalExterior := ExteriorAlgebra ℂ FormalOrbital

def formalJet (j : ℕ) : FormalExterior := ExteriorAlgebra.ι ℂ (Finsupp.single j 1)

/-- Original normalized v_p, with its original unordered two-form coefficient. -/
def formalPair (p : ℕ) : FormalExterior :=
  ∑ i : Fin (p+2), (pairLeftCoefficient p i.val : ℂ) •
    (formalJet i.val * formalJet (p+1-i.val))

/-- Original w_{D,r}=sum S_r v_p wedge e_j wedge e_k. -/
def formalCoupledColumn (D : ℕ) (r : OddMode D) : FormalExterior :=
  ∑ q : InputIndex D, maskedS45 D r q •
    (formalPair q.1.val * formalJet q.2.val * formalJet (D-q.1.val-q.2.val))

def rawJetOrbitalMap (G : Geometry) (theta : Twist) (R : ℂ) :
    FormalOrbital →ₗ[ℂ] Orbital (physicalQ G theta) :=
  Finsupp.linearCombination ℂ (fun j => physicalJetCoordinates G theta j R)

def rawJetExteriorMap (G : Geometry) (theta : Twist) (R : ℂ) :
    FormalExterior →ₐ[ℂ] Space (physicalQ G theta) :=
  ExteriorAlgebra.map (rawJetOrbitalMap G theta R)

def physicalCoupledColumn (G : Geometry) (theta : Twist) (D : ℕ)
    (r : OddMode D) (R : ℂ) : Space (physicalQ G theta) :=
  rawJetExteriorMap G theta R (formalCoupledColumn D r)

theorem rawJetExteriorMap_jet (G : Geometry) (theta : Twist) (R : ℂ) (j : ℕ) :
    rawJetExteriorMap G theta R (formalJet j) =
      ExteriorAlgebra.ι ℂ (physicalJetCoordinates G theta j R) := by
  simp only [rawJetExteriorMap,formalJet,ExteriorAlgebra.map_apply_ι,
    rawJetOrbitalMap,Finsupp.linearCombination_single,one_smul]

theorem rawJetExteriorMap_pair (G : Geometry) (theta : Twist) (R : ℂ) (p : ℕ) :
    rawJetExteriorMap G theta R (formalPair p) =
      ∑ i : Fin (p+2), (pairLeftCoefficient p i.val : ℂ) •
        (ExteriorAlgebra.ι ℂ (physicalJetCoordinates G theta i.val R) *
          ExteriorAlgebra.ι ℂ (physicalJetCoordinates G theta (p+1-i.val) R)) := by
  simp only [formalPair,map_sum,map_smul,map_mul,rawJetExteriorMap_jet]

private theorem jet_mul_adjoint (G : Geometry) (theta : Twist) (R : ℂ) (j : ℕ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (ExteriorAlgebra.ι ℂ (physicalJetCoordinates G theta j R) * x) y =
    occupationInner (physicalQ G theta) x (localJetAnnihilate G theta j R y) :=
  rawCreate_adjoint (physicalQ G theta) (physicalJetCoordinates G theta j R) x y

private theorem pair_mul_adjoint (G : Geometry) (theta : Twist) (R : ℂ) (p : ℕ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (rawJetExteriorMap G theta R (formalPair p) * x) y =
    occupationInner (physicalQ G theta) x (pairDescendant G theta p R y) := by
  rw [rawJetExteriorMap_pair,pairDescendant_eq_paper,paperPairDescendant_single_sum]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
    occupationInner_smul_left,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_right,occupationInner_smul_right,Module.End.mul_apply,
    mul_assoc,jet_mul_adjoint,Complex.star_def,Complex.conj_ofReal]

/-- A(w^T_{D,r}) is the genuine occupation adjoint of creation by the actual
exterior image (wedge^4 C_R) w_{D,r}. This proves the physical identification. -/
theorem physicalCoupledColumn_mul_adjoint (G : Geometry) (theta : Twist)
    (D : ℕ) (r : OddMode D) (R : ℂ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) (physicalCoupledColumn G theta D r R * x) y =
      occupationInner (physicalQ G theta) x (coupledFourAmplitude G theta D r R y) := by
  simp only [physicalCoupledColumn,formalCoupledColumn,map_sum,map_smul,map_mul,
    rawJetExteriorMap_jet,Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
    occupationInner_smul_left,maskedS45_star,coupledFourAmplitude,
    occupationInner_sum_right,occupationInner_smul_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_assoc,mul_assoc,pair_mul_adjoint,jet_mul_adjoint,jet_mul_adjoint]
  rfl

/-- Actual zero wedge columns give zero CAR amplitudes; they need never be
removed or treated as independent in a subsequent kernel-preserving transfer. -/
theorem coupledFourAmplitude_zero_of_column_zero (G : Geometry) (theta : Twist)
    (D : ℕ) (r : OddMode D) (R : ℂ) (h : physicalCoupledColumn G theta D r R=0)
    (y : Space (physicalQ G theta)) : coupledFourAmplitude G theta D r R y=0 := by
  have he := physicalCoupledColumn_mul_adjoint G theta D r R
    (coupledFourAmplitude G theta D r R y) y
  rw [h,zero_mul,occupationInner_self] at he
  have hn : occupationNormSq (physicalQ G theta) (coupledFourAmplitude G theta D r R y)=0 := by
    have hc := congrArg Complex.re he
    simpa only [occupationInner, map_zero, Finsupp.zero_apply,star_zero,zero_mul,
      Finset.sum_const_zero,Complex.zero_re,Complex.ofReal_re] using hc.symm
  exact (occupationNormSq_eq_zero _ _).mp hn

#print axioms rawJetExteriorMap_jet
#print axioms rawJetExteriorMap_pair
#print axioms physicalCoupledColumn_mul_adjoint
#print axioms coupledFourAmplitude_zero_of_column_zero
end TorusLean.Shared.FermionLocalJet.FourCoupling
