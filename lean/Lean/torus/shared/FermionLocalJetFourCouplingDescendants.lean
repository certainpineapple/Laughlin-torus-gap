import torus.shared.FermionLocalJetFourCouplingComplete

/-! Genuine full-Fock amplitudes for every original fixed-T coupled row,
with COM degree T-D. Complete coefficient reconstruction is applied to the
actual raw-jet CAR inputs, including their antisymmetric ordered extension. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.PhysicalFermionNormalSquare
open scoped BigOperators ComplexConjugate

def descendantFourAmplitude (G : Geometry) (theta : Twist) (D T r : ℕ)
    (R : ℂ) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  ∑ q : HalfInputIndex T,
    paperS45 r D T q.val.1.val q.val.2.val (T-q.val.1.val-q.val.2.val) •
      fourInputAmplitude G theta q.val.1.val q.val.2.val (T-q.val.1.val-q.val.2.val) R x

theorem fourInputAmplitude_exchange (G : Geometry) (theta : Twist)
    (p j k : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    fourInputAmplitude G theta p j k R x = -fourInputAmplitude G theta p k j R x :=
  vectorAnnihilate_anticomm_apply _ _ _ _

theorem fourInputAmplitude_diagonal (G : Geometry) (theta : Twist)
    (p j : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    fourInputAmplitude G theta p j j R x = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem paperS45_diagonal_odd (r D T p j : ℕ) (hr : Odd r) :
    paperS45 r D T p j j=0 := by
  have h := paperS45_exchange_odd r D T p j j hr
  linear_combination (1/2:ℂ)*h

/-- At COM level zero, this is exactly the previously verified actual
highest-weight A(w^T_Dr), with the same j<k and sqrt2 normalization. -/
theorem descendantFourAmplitude_highest (G : Geometry) (theta : Twist)
    (D : ℕ) (r : OddMode D) (R : ℂ) (x : Space (physicalQ G theta)) :
    descendantFourAmplitude G theta D D r.val.val R x = coupledFourAmplitude G theta D r R x := by
  classical
  unfold descendantFourAmplitude
  rw [halfInput_sum D (fun q : InputIndex D =>
    paperS45 r.val.val D D q.1.val q.2.val (D-q.1.val-q.2.val) •
      fourInputAmplitude G theta q.1.val q.2.val (D-q.1.val-q.2.val) R x)]
  simp only [coupledFourAmplitude,Fintype.sum_sigma,maskedS45]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro j hj
  rw [← highestS45_eq_paper D r.val.val (Nat.le_of_lt_succ r.val.isLt)]
  split_ifs <;> simp

/-- Exact inverse S-transform on the true physical input coordinates. -/
theorem descendantFourAmplitude_reconstruct_half (G : Geometry) (theta : Twist)
    (T : ℕ) (q : HalfInputIndex T) (R : ℂ) (x : Space (physicalQ G theta)) :
    fourInputAmplitude G theta q.val.1.val q.val.2.val (T-q.val.1.val-q.val.2.val) R x =
      ∑ c : HalfInputIndex T, completeS45 T c q •
        descendantFourAmplitude G theta (fullCopyDegree T c) T (fullCopyRelative T c) R x := by
  exact (completeS45_reconstruct T
    (fun v => fourInputAmplitude G theta v.val.1.val v.val.2.val
      (T-v.val.1.val-v.val.2.val) R x) q).symm

/-- Original ordered spectator indices, with no restriction to j<k in the
row entries. Both the physical CAR input and its coefficient change sign. -/
theorem descendantFourAmplitude_reconstruct (G : Geometry) (theta : Twist)
    (T p j k : ℕ) (ht : p+j+k=T) (R : ℂ) (x : Space (physicalQ G theta)) :
    fourInputAmplitude G theta p j k R x =
      ∑ c : HalfInputIndex T,
        paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T p j k •
          descendantFourAmplitude G theta (fullCopyDegree T c) T (fullCopyRelative T c) R x := by
  classical
  have hh (a b : ℕ) (hab : a<b) (habT : p+a+b=T) :
      fourInputAmplitude G theta p a b R x =
        ∑ c : HalfInputIndex T,
          paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T p a b •
            descendantFourAmplitude G theta (fullCopyDegree T c) T (fullCopyRelative T c) R x := by
    have hp : p<T+1 := by omega
    have ha : a<T-p+1 := by omega
    have hab' : a<T-p-a := by omega
    let q : HalfInputIndex T := ⟨⟨⟨p,hp⟩,⟨a,ha⟩⟩,hab'⟩
    have hk : T-p-a=b := by omega
    simpa only [q,hk,completeS45] using descendantFourAmplitude_reconstruct_half G theta T q R x
  rcases lt_trichotomy j k with h | h | h
  · exact hh j k h ht
  · subst k
    rw [fourInputAmplitude_diagonal]
    have hz (c : HalfInputIndex T) :
        paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T p j j=0 :=
      paperS45_diagonal_odd _ _ _ _ _ (fullCopy_range T c).1
    simp only [hz,zero_smul,Finset.sum_const_zero]
  · rw [fourInputAmplitude_exchange,hh k j h (by omega)]
    have hs (c : HalfInputIndex T) :
        paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T p k j =
          -paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T p j k :=
      paperS45_exchange_odd _ _ _ _ _ _ (fullCopy_range T c).1
    simp only [hs,neg_smul,Finset.sum_neg_distrib,neg_neg]

#print axioms fourInputAmplitude_exchange
#print axioms fourInputAmplitude_diagonal
#print axioms paperS45_diagonal_odd
#print axioms descendantFourAmplitude_highest
#print axioms descendantFourAmplitude_reconstruct_half
#print axioms descendantFourAmplitude_reconstruct
end TorusLean.Shared.FermionLocalJet.FourCoupling
