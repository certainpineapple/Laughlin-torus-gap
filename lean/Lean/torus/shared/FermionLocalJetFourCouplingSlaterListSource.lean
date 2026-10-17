import torus.shared.FermionLocalJetFourCouplingSlaterListNormalize
import torus.shared.FermionLocalJetFourCouplingSlaterListCoefficient

/-! Both executable lists are proved presentations of the original Finsupps.
All original half-inputs, odd labels, signs and factorial coefficients remain. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
namespace SlaterListCandidate

theorem evalTerms_flatMap {α : Type*} (l : List α) (f : α → List Term) :
    evalTerms (l.flatMap f)=(l.map (fun a => evalTerms (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons,evalTerms_append,ih,List.map_cons,List.sum_cons]

def sourceTerms (D T r : ℕ) : List Term :=
  (List.finRange (T+1)).flatMap (fun p =>
    (List.finRange (T-p.val+1)).flatMap (fun j =>
      if j.val<T-p.val-j.val then
        (List.finRange (p.val+2)).map (fun a =>
          ((a.val,p.val+1-a.val,j.val,T-p.val-j.val),
            pairCoefficientList D T r p.val j.val (T-p.val-j.val) a.val))
      else []))

theorem sourceTerms_eval (D T r : ℕ) (hrD : r≤D) (hDT : D≤T) :
    evalTerms (sourceTerms D T r)=integerSourceWords D T r := by
  classical
  have hexpand : evalTerms (sourceTerms D T r) =
      ∑ p : Fin (T+1), ∑ j : Fin (T-p.val+1),
        if j.val<T-p.val-j.val then
          ∑ a : Fin (p.val+2), termWord
            ((a.val,p.val+1-a.val,j.val,T-p.val-j.val),
              pairCoefficientList D T r p.val j.val (T-p.val-j.val) a.val)
        else 0 := by
    simp only [sourceTerms,evalTerms_flatMap,Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro p hp
    congr 1
    apply List.map_congr_left
    intro j hj
    split_ifs
    · simp only [evalTerms,List.map_map,Function.comp_def]
    · rfl
  rw [hexpand,integerSourceWords,
    halfInput_sum T (fun q : InputIndex T =>
      ∑ a : Fin (q.1.val+2), Finsupp.single
        ![a.val,q.1.val+1-a.val,q.2.val,T-q.1.val-q.2.val]
        (integerPairSpectatorCoefficient D T r q.1.val q.2.val
          (T-q.1.val-q.2.val) a.val))]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · apply Finset.sum_congr rfl
    intro a ha
    have hT : p.val+j.val+(T-p.val-j.val)=T := by
      have hpb := p.isLt
      have hjb := j.isLt
      omega
    rw [integerPairSpectatorCoefficient_eq_list D T r p.val j.val
      (T-p.val-j.val) a.val hrD hDT hT]
    rfl
  · rfl

def slaterTerms (D r : ℕ) : List Term :=
  (OAI.Laughlin.Certificate.quadruples D).map (fun A => (A,integerSlaterNumerator D r A))

theorem slaterTerms_eval (D r : ℕ) :
    evalTerms (slaterTerms D r)=integerSlaterWords D r := by
  change evalTerms (slaterTerms D r) =
    ∑ A : SlaterIndex D, Finsupp.single (labels (slaterTuple D A))
      (integerSlaterNumerator D r (slaterTuple D A))
  rw [slaterIndex_sum D (fun A : FourTuple =>
    Finsupp.single (labels A) (integerSlaterNumerator D r A))]
  simp only [evalTerms,slaterTerms,List.map_map,termWord,Function.comp_def]

/-- Only a finite list equality remains. This lemma's conclusion is precisely
the original source identity, with no domain restriction or kernel assumption. -/
theorem originalSlaterSource_of_list_check (D : ℕ)
    (hcheck : ∀ r : OddMode D, normalizeTerms (sourceTerms D D r.val.val)=
      normalizeTerms (slaterTerms D r.val.val)) :
    ∀ r : OddMode D, alternateIntegerFourWords (integerSourceWords D D r.val.val)=
      alternateIntegerFourWords (integerSlaterWords D r.val.val) := by
  intro r
  rw [← sourceTerms_eval D D r.val.val (Nat.le_of_lt_succ r.val.isLt) le_rfl,
    ← slaterTerms_eval D r.val.val]
  exact alternate_eq_of_normalizeTerms_eq _ _ (hcheck r)

end SlaterListCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_flatMap
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceTerms_eval
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.slaterTerms_eval
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.originalSlaterSource_of_list_check
