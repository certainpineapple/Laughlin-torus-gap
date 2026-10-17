import torus.shared.FermionLocalJetFourCouplingFirstRelative

/-! The original r=1 physical copy equals C_{D-1}, with no rescaling or
index change beyond D=d+1. Both true pair annihilators commute by CAR. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.RelativeJetMap
open scoped BigOperators ComplexConjugate

def targetMode (d : ℕ) : OddMode (d+1) := ⟨⟨1,by omega⟩,by change Odd (1:ℕ); decide⟩

/-- The r=1 highest-weight row is the product of the original C_d binomial
and original unordered v_{d-p} pair coefficient, with its negative sign. -/
theorem highestS45_target_coefficient (d p j : ℕ) (hp : p≤d) :
    (if j<d+1-p-j then highestS45 (d+1) 1 p j else 0) =
      relativeBinomialCoeff d p * (pairLeftCoefficient (d-p) j : ℂ) := by
  have hn : d+1-p=d-p+1 := by omega
  by_cases hj : j<d+1-p-j
  · have hs : j+(d-p+1-j)=d-p+1 := by omega
    rw [if_pos hj]
    unfold highestS45 highestOrderedCoefficient
    rw [Nat.add_sub_cancel,s45_highest_relative d p hp,hn,← mul_assoc,
      s45_first_relative (d-p) j (d-p+1-j) hs]
    simp only [pairLeftCoefficient,show j<d-p+1-j by omega,if_true]
    push_cast <;> ring
  · have hj' : ¬j<d-p+1-j := by omega
    simp only [if_neg hj,pairLeftCoefficient,if_neg hj',Complex.ofReal_zero,mul_zero]

private theorem target_last_zero (d j : ℕ) :
    (if j<d+1-(d+1)-j then highestS45 (d+1) 1 (d+1) j else 0)=0 := by simp

/-- Genuine coupled annihilation of w_{d+1,1} equals the original paper C_d
on the entire Fock space, using the original pair CAR commutation. -/
theorem coupledFourAmplitude_target (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    coupledFourAmplitude G theta (d+1) (targetMode d) R x = paperFourBodyJet G theta d R x := by
  let F (p j : ℕ) : Space (physicalQ G theta) :=
    (if j<d+1-p-j then highestS45 (d+1) 1 p j else 0) •
      fourInputAmplitude G theta p j (d+1-p-j) R x
  have hex : coupledFourAmplitude G theta (d+1) (targetMode d) R x =
      ∑ p ∈ Finset.range (d+2), ∑ j ∈ Finset.range (d+1-p+1), F p j := by
    simp only [coupledFourAmplitude,Fintype.sum_sigma,maskedS45,targetMode]
    change (∑ p : Fin (d+2), ∑ j : Fin (d+1-p.val+1), F p.val j.val) = _
    calc
      _ = ∑ p : Fin (d+2), ∑ j ∈ Finset.range (d+1-p.val+1), F p.val j :=
        Finset.sum_congr rfl (fun p _ => Fin.sum_univ_eq_sum_range (fun j => F p.val j) _)
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun p => ∑ j ∈ Finset.range (d+1-p+1), F p j) (d+2)
  rw [hex,← fourBodyJet_eq_paper]
  simp only [fourBodyJet,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
  rw [Finset.sum_range_succ]
  dsimp only [F]
  simp only [target_last_zero,zero_smul,Finset.sum_const_zero,add_zero]
  apply Finset.sum_congr rfl
  intro p hp
  have hpd : p≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  have hn : d+1-p+1=d-p+2 := by omega
  simp_rw [highestS45_target_coefficient d p _ hpd,mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  have hpair := LinearMap.congr_fun (paperPairDescendant_single_sum G theta (d-p) R)
    (pairDescendant G theta p R x)
  rw [← pairDescendant_eq_paper] at hpair
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply] at hpair
  rw [Fin.sum_univ_eq_sum_range (fun j => (pairLeftCoefficient (d-p) j : ℂ) •
    localJetAnnihilate G theta (d-p+1-j) R
      (localJetAnnihilate G theta j R (pairDescendant G theta p R x))) (d-p+2)] at hpair
  have hs : (∑ j ∈ Finset.range (d+1-p+1), (pairLeftCoefficient (d-p) j : ℂ) •
      fourInputAmplitude G theta p j (d+1-p-j) R x) =
      pairDescendant G theta (d-p) R (pairDescendant G theta p R x) := by
    rw [hn]
    have hn' : d+1-p=d-p+1 := by omega
    simpa only [fourInputAmplitude,hn'] using hpair.symm
  exact hs.trans (LinearMap.congr_fun (pairDescendant_commute G theta (d-p) p R R) x)

/-- Physical target copy in the actual raw-jet exterior image, identified as
an occupation adjoint with the manuscript C_d on the original Fock carrier. -/
theorem physicalCoupledColumn_target_adjoint (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (physicalCoupledColumn G theta (d+1) (targetMode d) R * x) y =
      occupationInner (physicalQ G theta) x (paperFourBodyJet G theta d R y) := by
  rw [physicalCoupledColumn_mul_adjoint,coupledFourAmplitude_target]

/-- Exact factor 2 for the original target energy: D=d+1 and mu4=2mu2.
All twenty-three original relative degrees are retained. -/
theorem target_copy_energy (G : Geometry) (theta : Twist) (x : Space (physicalQ G theta)) :
    2 * (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
      (coupledFourAmplitude G theta (d.val+1) (targetMode d.val) R x) ∂cellMeasure G 2) =
    ∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
      (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4 := by
  rw [cellIntegral_four_eq_two]
  simp_rw [coupledFourAmplitude_target]

#print axioms highestS45_target_coefficient
#print axioms coupledFourAmplitude_target
#print axioms physicalCoupledColumn_target_adjoint
#print axioms target_copy_energy
end TorusLean.Shared.FermionLocalJet.FourCoupling
