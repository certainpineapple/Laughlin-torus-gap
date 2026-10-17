import torus.shared.FermionLocalJetFourCouplingSlaterListFastNormalize

/-! Resource-bounded proof composition over the ORIGINAL outer source index p.
Every block and every finite merge is separately certified; no witness list is
assumed equal to an original source or used without a corresponding proof. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
namespace SlaterListCandidate

def sourceBlock (D T r p : ℕ) : List Term :=
  (List.finRange (T-p+1)).flatMap (fun j =>
    if j.val<T-p-j.val then
      (List.finRange (p+2)).map (fun a =>
        ((a.val,p+1-a.val,j.val,T-p-j.val),
          pairCoefficientList D T r p j.val (T-p-j.val) a.val))
    else [])

def sourceBlocks (D T r : ℕ) : List (List Term) :=
  (List.finRange (T+1)).map (fun p => sourceBlock D T r p.val)

theorem sourceBlocks_flatten (D T r : ℕ) :
    (sourceBlocks D T r).flatten=sourceTerms D T r := by
  rfl

def mergeTerms (l k : List Term) : List Term := dropZero (collectTerms (l++k))

theorem evalTerms_merge (l k : List Term) :
    evalTerms (mergeTerms l k)=evalTerms l+evalTerms k := by
  rw [mergeTerms,evalTerms_dropZero,evalTerms_collect,evalTerms_append]

def foldNormalBlocks (acc : List Term) : List (List Term) → List Term
  | [] => acc
  | b::bs => foldNormalBlocks (mergeTerms acc (normalizeTermsFast b)) bs

theorem alternate_foldNormalBlocks (acc : List Term) (bs : List (List Term)) :
    alternateIntegerFourWords (evalTerms (foldNormalBlocks acc bs))=
      alternateIntegerFourWords (evalTerms acc)+
        alternateIntegerFourWords (evalTerms bs.flatten) := by
  induction bs generalizing acc with
  | nil => simp only [foldNormalBlocks,List.flatten_nil,evalTerms_nil,map_zero,add_zero]
  | cons b bs ih =>
    rw [foldNormalBlocks,ih,evalTerms_merge,map_add,alternate_normalizeTermsFast]
    simp only [List.flatten_cons,evalTerms_append,map_add,add_assoc]

theorem originalSlaterMode_of_blocks_check (D r : ℕ) (hrD : r≤D)
    (h : foldNormalBlocks [] (sourceBlocks D D r)=normalizeTermsFast (slaterTerms D r)) :
    alternateIntegerFourWords (integerSourceWords D D r)=
      alternateIntegerFourWords (integerSlaterWords D r) := by
  have he := congrArg (fun l : List Term => alternateIntegerFourWords (evalTerms l)) h
  rw [alternate_foldNormalBlocks,evalTerms_nil,map_zero,zero_add,sourceBlocks_flatten,
    sourceTerms_eval D D r hrD le_rfl,alternate_normalizeTermsFast,slaterTerms_eval] at he
  exact he

theorem originalSlaterMode_of_fast_list_check (D r : ℕ) (hrD : r≤D)
    (h : normalizeTermsFast (sourceTerms D D r)=normalizeTermsFast (slaterTerms D r)) :
    alternateIntegerFourWords (integerSourceWords D D r)=
      alternateIntegerFourWords (integerSlaterWords D r) := by
  rw [← sourceTerms_eval D D r hrD le_rfl,← slaterTerms_eval D r]
  exact alternate_eq_of_normalizeTermsFast_eq _ _ h

end SlaterListCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceBlocks_flatten
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_merge
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_foldNormalBlocks
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.originalSlaterMode_of_blocks_check
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.originalSlaterMode_of_fast_list_check
