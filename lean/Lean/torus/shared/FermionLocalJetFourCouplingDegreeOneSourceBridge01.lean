import torus.shared.FermionLocalJetFourCouplingDegreeOneAlgebra01

/- Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open DegreeOneAlgebraCandidate
namespace DegreeOneSourceBridgeCandidate

abbrev SourceIndex (T : ℕ) := (q : HalfInputIndex T) × Fin (q.val.1.val+2)

def sourceWord {T : ℕ} (x : SourceIndex T) : Fin 4 → ℕ :=
  ![x.2.val,x.1.val.1.val+1-x.2.val,x.1.val.2.val,T-x.1.val.1.val-x.1.val.2.val]

theorem sourceWord_injective (T : ℕ) : Function.Injective (sourceWord (T:=T)) := by
  intro x y h
  rcases x with ⟨⟨⟨p,j⟩,hq⟩,a⟩
  rcases y with ⟨⟨⟨p',j'⟩,hq'⟩,a'⟩
  have h0 := congrFun h (0 : Fin 4)
  change a.val=a'.val at h0
  have h1 := congrFun h (1 : Fin 4)
  change p.val+1-a.val=p'.val+1-a'.val at h1
  have h2 := congrFun h (2 : Fin 4)
  change j.val=j'.val at h2
  have hp : p=p' := by
    apply Fin.ext
    have ha : a.val < p.val+2 := a.isLt
    have ha' : a'.val < p'.val+2 := a'.isLt
    omega
  subst p'
  have hj : j=j' := Fin.ext h2
  subst j'
  have ha : a=a' := Fin.ext h0
  subst a'
  rfl

theorem sourceWord_total {T : ℕ} (x : SourceIndex T) :
    (∑ i : Fin 4, sourceWord x i)=T+1 := by
  have hp : x.1.val.1.val < T+1 := x.1.val.1.isLt
  have hj : x.1.val.2.val < T-x.1.val.1.val+1 := x.1.val.2.isLt
  have ha : x.2.val < x.1.val.1.val+2 := x.2.isLt
  rw [Fin.sum_univ_four]
  change x.2.val + (x.1.val.1.val+1-x.2.val) + x.1.val.2.val +
    (T-x.1.val.1.val-x.1.val.2.val) = T+1
  omega

theorem sourceWord_exists (T : ℕ) (w : Fin 4 → ℕ)
    (htotal : (∑ i : Fin 4, w i)=T+1) (h01 : w 0<w 1) (h23 : w 2<w 3) :
    ∃ x : SourceIndex T, sourceWord x=w := by
  have hw : w 0+w 1+w 2+w 3=T+1 := by
    simpa only [Fin.sum_univ_four] using htotal
  let p : Fin (T+1) := ⟨w 0+w 1-1,by omega⟩
  let j : Fin (T-p.val+1) := ⟨w 2,by dsimp [p]; omega⟩
  have hk : T-p.val-j.val=w 3 := by dsimp [p,j]; omega
  let q : HalfInputIndex T := ⟨⟨p,j⟩,by
    change j.val<T-p.val-j.val
    rw [hk]
    exact h23⟩
  let a : Fin (q.val.1.val+2) := ⟨w 0,by dsimp [q,p]; omega⟩
  refine ⟨⟨q,a⟩,?_⟩
  funext i
  fin_cases i <;> simp [sourceWord,q,a,p,j] <;> omega

theorem source_as_singleSum (T : ℕ) :
    integerSourceWords 1 T 1 =
      ∑ x : SourceIndex T, Finsupp.single (sourceWord x)
        (halfKernel (sourceWord x) * ((T-1).factorial : ℤ)) := by
  classical
  rw [integerSourceWords_closed,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (Finsupp.single (sourceWord ⟨q,a⟩))
  change
    (if a.val < q.val.1.val+1-a.val then
      ((a.val : ℤ)-((q.val.1.val+1-a.val : ℕ) : ℤ)) *
      ((q.val.2.val : ℤ)-((T-q.val.1.val-q.val.2.val : ℕ) : ℤ)) *
      ((T-1).factorial : ℤ)
     else 0) =
    (pairCut a.val (q.val.1.val+1-a.val) *
      pairCut q.val.2.val (T-q.val.1.val-q.val.2.val)) * ((T-1).factorial : ℤ)
  have hq23 : q.val.2.val < T-q.val.1.val-q.val.2.val := q.property
  unfold pairCut
  rw [if_pos hq23]
  split_ifs <;> simp

theorem source_generated (T : ℕ) (x : SourceIndex T) :
    (integerSourceWords 1 T 1) (sourceWord x) =
      halfKernel (sourceWord x) * ((T-1).factorial : ℤ) := by
  classical
  rw [source_as_singleSum,Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hyx
    exact Finsupp.single_eq_of_ne' ((sourceWord_injective T).ne hyx)
  · simp

theorem source_apply (T : ℕ) (w : Fin 4 → ℕ) :
    (integerSourceWords 1 T 1) w =
      if (∑ i : Fin 4, w i)=T+1 then halfKernel w * ((T-1).factorial : ℤ) else 0 := by
  classical
  by_cases hex : ∃ x : SourceIndex T, sourceWord x=w
  · obtain ⟨x,rfl⟩ := hex
    rw [source_generated,if_pos (sourceWord_total x)]
  · have hs : (integerSourceWords 1 T 1) w=0 := by
      rw [source_as_singleSum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro x hx
      apply Finsupp.single_eq_of_ne'
      intro he
      exact hex ⟨x,he⟩
    rw [hs]
    by_cases ht : (∑ i : Fin 4, w i)=T+1
    · by_cases h01 : w 0<w 1
      · by_cases h23 : w 2<w 3
        · exact False.elim (hex (sourceWord_exists T w ht h01 h23))
        · simp [ht,halfKernel,pairCut,h23]
      · simp [ht,halfKernel,pairCut,h01]
    · simp [ht]

theorem permute_apply (σ : Equiv.Perm (Fin 4)) (c : IntegerFourWords) (w : Fin 4 → ℕ) :
    (permuteIntegerFourWords σ c) w = c (w ∘ σ.symm) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.coe_zero,Pi.zero_apply]
  | add c d hc hd => simp only [map_add,Finsupp.add_apply,hc,hd]
  | single v a =>
    have hi : (v ∘ σ=w) ↔ (v=w ∘ σ.symm) := by
      constructor
      · intro h
        funext i
        have hh := congrFun h (σ.symm i)
        simpa only [Function.comp_apply,σ.apply_symm_apply] using hh
      · intro h
        subst v
        funext i
        simp only [Function.comp_apply,σ.symm_apply_apply]
    simp only [permuteIntegerFourWords,Finsupp.linearCombination_single,
      Finsupp.smul_single,smul_eq_mul,mul_one,Finsupp.single_apply,hi]

theorem alternate_apply (c : IntegerFourWords) (w : Fin 4 → ℕ) :
    (alternateIntegerFourWords c) w = alt (fun v => c v) w := by
  classical
  simp only [alternateIntegerFourWords,LinearMap.sum_apply,Finsupp.finsetSum_apply,
    LinearMap.smul_apply,Finsupp.smul_apply,smul_eq_mul,permute_apply]
  unfold alt
  apply Fintype.sum_bijective (fun σ : Equiv.Perm (Fin 4) => σ⁻¹)
    inv_involutive.bijective
  intro σ
  simp only [Equiv.Perm.inv_def,Equiv.Perm.sign_symm]

theorem original_source_alternate_zero (T : ℕ) :
    alternateIntegerFourWords (integerSourceWords 1 T 1)=0 := by
  classical
  ext w
  rw [alternate_apply]
  change alt (fun v => (integerSourceWords 1 T 1) v) w=0
  unfold alt
  simp_rw [source_apply]
  have ht (σ : Equiv.Perm (Fin 4)) : (∑ i : Fin 4, (w ∘ σ) i)=∑ i : Fin 4, w i := by
    simpa only [Function.comp_apply] using Equiv.sum_comp σ w
  simp_rw [ht]
  by_cases hw : (∑ i : Fin 4, w i)=T+1
  · simp only [hw,ite_true]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    change alt halfKernel w * ((T-1).factorial : ℤ)=0
    rw [alt_halfKernel_zero,zero_mul]
  · simp [hw]

end DegreeOneSourceBridgeCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.sourceWord_injective
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.sourceWord_total
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.sourceWord_exists
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.source_as_singleSum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.source_generated
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.source_apply
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.permute_apply
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.alternate_apply
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneSourceBridgeCandidate.original_source_alternate_zero
