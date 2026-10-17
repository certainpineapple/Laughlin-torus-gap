import torus.shared.FermionLocalJetFourCouplingSlaterPresentation
import torus.shared.FermionLocalJetFourCouplingGeneralHalfSpace

/-! Exact finite-list presentation of the original integer alternating map.
Every transformation below preserves that map; no source, Gram, or physical
identity is assumed. Computation is confined to lists of natural/integer tuples. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
namespace SlaterListCandidate

abbrev FourTuple := ℕ × ℕ × ℕ × ℕ
abbrev Term := FourTuple × ℤ

def labels (A : FourTuple) : Fin 4 → ℕ := ![A.1,A.2.1,A.2.2.1,A.2.2.2]
def tuple (w : Fin 4 → ℕ) : FourTuple := (w 0,w 1,w 2,w 3)
def termWord (t : Term) : IntegerFourWords := Finsupp.single (labels t.1) t.2
def evalTerms (l : List Term) : IntegerFourWords := (l.map termWord).sum

theorem labels_tuple (w : Fin 4 → ℕ) : labels (tuple w)=w := by
  funext i
  fin_cases i <;> rfl

theorem evalTerms_nil : evalTerms []=0 := rfl

theorem evalTerms_cons (t : Term) (l : List Term) :
    evalTerms (t::l)=termWord t+evalTerms l := rfl

theorem evalTerms_append (l k : List Term) :
    evalTerms (l++k)=evalTerms l+evalTerms k := by
  simp only [evalTerms,List.map_append,List.sum_append]

theorem termWord_add (A : FourTuple) (a b : ℤ) :
    termWord (A,a+b)=termWord (A,a)+termWord (A,b) := by
  simp only [termWord,Finsupp.single_add]

theorem termWord_zero (A : FourTuple) : termWord (A,0)=0 := by
  simp only [termWord,Finsupp.single_zero]

/-- The tuple implementation of a swap is fully executable. -/
def swapTuple (i j : Fin 4) (A : FourTuple) : FourTuple :=
  tuple (labels A ∘ Equiv.swap i j)

theorem labels_swapTuple (i j : Fin 4) (A : FourTuple) :
    labels (swapTuple i j A)=labels A ∘ Equiv.swap i j := labels_tuple _

theorem alternate_term_swap (A : FourTuple) (a : ℤ) (i j : Fin 4) (hij : i≠j) :
    alternateIntegerFourWords (termWord (swapTuple i j A,a)) =
      -alternateIntegerFourWords (termWord (A,a)) := by
  have h := GeneralHalfSpaceCandidate.alternate_permute_swap (termWord (A,a)) i j hij
  simpa only [termWord,permuteIntegerFourWords,Finsupp.linearCombination_single,
    Finsupp.smul_single,smul_eq_mul,mul_one,labels_swapTuple] using h

theorem alternate_term_repeated (A : FourTuple) (a : ℤ) (i j : Fin 4)
    (hij : i≠j) (heq : labels A i=labels A j) :
    alternateIntegerFourWords (termWord (A,a))=0 := by
  have hv := GeneralHalfSpaceCandidate.swap_vec_fixed_of_eq (labels A) i j heq
  have h := alternate_term_swap A a i j hij
  have hs : termWord (swapTuple i j A,a)=termWord (A,a) := by
    simp only [termWord,labels_swapTuple,hv]
  rw [hs] at h
  ext w
  have hw := congrArg (fun f : IntegerFourWords => f w) h
  simp only [Finsupp.neg_apply] at hw
  change (alternateIntegerFourWords (termWord (A,a))) w=0
  omega

/-- One adjacent compare/exchange, including its exact orientation sign. -/
def compareExchange (i j : Fin 4) (t : Term) : Term :=
  if labels t.1 i≤labels t.1 j then t else (swapTuple i j t.1,-t.2)

theorem alternate_compareExchange (i j : Fin 4) (hij : i≠j) (t : Term) :
    alternateIntegerFourWords (termWord (compareExchange i j t))=
      alternateIntegerFourWords (termWord t) := by
  unfold compareExchange
  split_ifs with h
  · rfl
  · rw [alternate_term_swap _ _ _ _ hij]
    simp only [termWord,Finsupp.single_neg,map_neg,neg_neg]

/-- A fixed six-comparator sorting network. Its correctness as a sorter is
unneeded for soundness: preservation follows from each explicit exchange. -/
def sortTerm (t : Term) : Term :=
  compareExchange 0 1 (compareExchange 1 2 (compareExchange 0 1
    (compareExchange 2 3 (compareExchange 1 2 (compareExchange 0 1 t)))))

theorem alternate_sortTerm (t : Term) :
    alternateIntegerFourWords (termWord (sortTerm t))=
      alternateIntegerFourWords (termWord t) := by
  unfold sortTerm
  rw [alternate_compareExchange _ _ (by decide),
    alternate_compareExchange _ _ (by decide),
    alternate_compareExchange _ _ (by decide),
    alternate_compareExchange _ _ (by decide),
    alternate_compareExchange _ _ (by decide),
    alternate_compareExchange _ _ (by decide)]

end SlaterListCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.labels_tuple
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_nil
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_cons
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_append
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.termWord_add
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.termWord_zero
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.labels_swapTuple
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_term_swap
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_term_repeated
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_compareExchange
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_sortTerm
