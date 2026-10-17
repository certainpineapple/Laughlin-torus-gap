import torus.shared.FermionLocalJetFourCouplingWedge
import PaperPauliCoefficients

/-! Genuine finite exterior three-body seeds for the original fermion
anchored construction. The Nat exterior source and its actual raw-jet map
are the already constructed m1 formalPair/formalJet, not a new Fock model.
The anchor has the original negative pair orientation. Its l=0,1 cases are
literal zero wedges; no normalized nonzero Slater state is assigned to them.
This file establishes actual creation/removal rows, not a COM trace. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators ComplexConjugate

/-- Pair COM p has orbital degree p+1; this word has particle number three
and total orbital degree p+j+1. The parameter charge is three. -/
def formalThreeSeed (p j : ℕ) : FormalExterior := formalPair p * formalJet j

def formalAnchoredSeed (l : ℕ) : FormalExterior := formalThreeSeed 0 l

/-- The paper's original fermionic relative orientation, (-1)^(z-p).
Its orbital degree is z+1, while its particle/parameter charge is three.
The finite insertion may have a kernel and is not asserted to be isometric. -/
def formalRelativeSeed (z : ℕ) : FormalExterior :=
  ∑ p ∈ Finset.range (z+1), (paperPauliCoefficient z p:ℂ) • formalThreeSeed p (z-p)

theorem formalPair_ground : formalPair 0 = -(formalJet 0 * formalJet 1) := by
  change (∑ i : Fin 2, (pairLeftCoefficient 0 i.val:ℂ) •
    (formalJet i.val * formalJet (1-i.val))) = _
  rw [Fin.sum_univ_two]
  norm_num [pairLeftCoefficient,paperPairWeight]

theorem formalAnchoredSeed_zero : formalAnchoredSeed 0=0 := by
  rw [formalAnchoredSeed,formalThreeSeed,formalPair_ground,neg_mul,mul_assoc]
  have hs : formalJet 1*formalJet 0=-(formalJet 0*formalJet 1) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [hs,mul_neg,← mul_assoc]
  simp only [formalJet,ExteriorAlgebra.ι_sq_zero,zero_mul,neg_zero]

theorem formalAnchoredSeed_one : formalAnchoredSeed 1=0 := by
  rw [formalAnchoredSeed,formalThreeSeed,formalPair_ground,neg_mul,mul_assoc]
  simp only [formalJet,ExteriorAlgebra.ι_sq_zero,mul_zero,neg_zero]

private theorem raw_jet_mul_adjoint (G : Geometry) (theta : Twist) (R : ℂ)
    (j : ℕ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (ExteriorAlgebra.ι ℂ (physicalJetCoordinates G theta j R)*x) y =
      occupationInner (physicalQ G theta) x (localJetAnnihilate G theta j R y) :=
  rawCreate_adjoint (physicalQ G theta) (physicalJetCoordinates G theta j R) x y

/-- The actual raw-jet image is the original pair creator's occupation
adjoint at every COM level, with no finite jet-norm cutoff assumption. -/
theorem formalPair_image_mul_adjoint (G : Geometry) (theta : Twist) (R : ℂ)
    (p : ℕ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (rawJetExteriorMap G theta R (formalPair p) * x) y =
      occupationInner (physicalQ G theta) x (pairDescendant G theta p R y) := by
  rw [rawJetExteriorMap_pair,pairDescendant_eq_paper,paperPairDescendant_single_sum]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
    occupationInner_smul_left,LinearMap.sum_apply,LinearMap.smul_apply,
    occupationInner_sum_right,occupationInner_smul_right,Module.End.mul_apply,
    mul_assoc,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [raw_jet_mul_adjoint]

/-- Exact whole-Fock row A(v_p wedge e_j)=c_j B_p, preserving CAR order. -/
theorem formalThreeSeed_image_mul_adjoint (G : Geometry) (theta : Twist) (R : ℂ)
    (p j : ℕ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (rawJetExteriorMap G theta R (formalThreeSeed p j) * x) y =
      occupationInner (physicalQ G theta) x
        (localJetAnnihilate G theta j R (pairDescendant G theta p R y)) := by
  rw [formalThreeSeed,map_mul,rawJetExteriorMap_jet,mul_assoc,
    formalPair_image_mul_adjoint,raw_jet_mul_adjoint]

/-- In particular the original anchor uses the unchanged B_R, including
its negative m=1 ground-pair orientation. -/
theorem formalAnchoredSeed_image_mul_adjoint (G : Geometry) (theta : Twist) (R : ℂ)
    (l : ℕ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (rawJetExteriorMap G theta R (formalAnchoredSeed l) * x) y =
      occupationInner (physicalQ G theta) x
        (localJetAnnihilate G theta l R
          (PhysicalFermionNormalSquare.pairAt G theta R y)) := by
  rw [formalAnchoredSeed,formalThreeSeed_image_mul_adjoint,pairDescendant_zero]

end TorusLean.Shared.ThermalCoherentFermionAnchored
