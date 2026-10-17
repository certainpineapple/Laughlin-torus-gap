import torus.shared.FermionLocalJetFourCouplingSlaterListAlgebra

/-! A proof-preserving executable normal form of finite integer word lists.
The finite equality check compares derived lists, never replacement arrays. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
namespace SlaterListCandidate

/-- Pairing is only an executable ordering key; soundness needs no injectivity. -/
def tupleKey (A : FourTuple) : ℕ := Nat.pair A.1 (Nat.pair A.2.1 (Nat.pair A.2.2.1 A.2.2.2))

def insertTerm (t : Term) : List Term → List Term
  | [] => [t]
  | u::l => if t.1=u.1 then (u.1,t.2+u.2)::l
      else if tupleKey t.1≤tupleKey u.1 then t::u::l else u::insertTerm t l

theorem evalTerms_insert (t : Term) (l : List Term) :
    evalTerms (insertTerm t l)=termWord t+evalTerms l := by
  induction l with
  | nil => simp only [insertTerm,evalTerms_cons,evalTerms_nil,add_zero]
  | cons u l ih =>
    simp only [insertTerm]
    split_ifs with he hle
    · rcases t with ⟨A,a⟩
      rcases u with ⟨B,b⟩
      dsimp only at he
      subst B
      simp only [evalTerms_cons,termWord_add,add_assoc]
    · rfl
    · rw [evalTerms_cons,ih,evalTerms_cons]
      abel

def collectTerms : List Term → List Term
  | [] => []
  | t::l => insertTerm t (collectTerms l)

theorem evalTerms_collect (l : List Term) : evalTerms (collectTerms l)=evalTerms l := by
  induction l with
  | nil => rfl
  | cons t l ih => rw [collectTerms,evalTerms_insert,ih,evalTerms_cons]

def dropZero : List Term → List Term
  | [] => []
  | t::l => if t.2=0 then dropZero l else t::dropZero l

theorem evalTerms_dropZero (l : List Term) : evalTerms (dropZero l)=evalTerms l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [dropZero]
    split_ifs with h
    · rw [ih,evalTerms_cons]
      rcases t with ⟨A,a⟩
      dsimp only at h
      subst a
      rw [termWord_zero,zero_add]
    · rw [evalTerms_cons,ih,evalTerms_cons]

def removeRepeated (t : Term) : Term :=
  if t.1.1=t.1.2.1 ∨ t.1.1=t.1.2.2.1 ∨ t.1.1=t.1.2.2.2 ∨
      t.1.2.1=t.1.2.2.1 ∨ t.1.2.1=t.1.2.2.2 ∨ t.1.2.2.1=t.1.2.2.2
  then (t.1,0) else t

theorem alternate_removeRepeated (t : Term) :
    alternateIntegerFourWords (termWord (removeRepeated t))=
      alternateIntegerFourWords (termWord t) := by
  unfold removeRepeated
  split_ifs with h
  · rw [termWord_zero,map_zero]
    symm
    rcases h with h|h|h|h|h|h
    · exact alternate_term_repeated t.1 t.2 0 1 (by decide) h
    · exact alternate_term_repeated t.1 t.2 0 2 (by decide) h
    · exact alternate_term_repeated t.1 t.2 0 3 (by decide) h
    · exact alternate_term_repeated t.1 t.2 1 2 (by decide) h
    · exact alternate_term_repeated t.1 t.2 1 3 (by decide) h
    · exact alternate_term_repeated t.1 t.2 2 3 (by decide) h
  · rfl

def normalizeTerm (t : Term) : Term := sortTerm (removeRepeated t)

theorem alternate_normalizeTerm (t : Term) :
    alternateIntegerFourWords (termWord (normalizeTerm t))=
      alternateIntegerFourWords (termWord t) := by
  rw [normalizeTerm,alternate_sortTerm,alternate_removeRepeated]

theorem alternate_evalTerms_map (l : List Term) :
    alternateIntegerFourWords (evalTerms (l.map normalizeTerm))=
      alternateIntegerFourWords (evalTerms l) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [List.map_cons,evalTerms_cons,map_add,alternate_normalizeTerm,ih]

def normalizeTerms (l : List Term) : List Term :=
  dropZero (collectTerms (l.map normalizeTerm))

theorem alternate_normalizeTerms (l : List Term) :
    alternateIntegerFourWords (evalTerms (normalizeTerms l))=
      alternateIntegerFourWords (evalTerms l) := by
  rw [normalizeTerms,evalTerms_dropZero,evalTerms_collect,alternate_evalTerms_map]

theorem alternate_eq_of_normalizeTerms_eq (l k : List Term)
    (h : normalizeTerms l=normalizeTerms k) :
    alternateIntegerFourWords (evalTerms l)=alternateIntegerFourWords (evalTerms k) := by
  rw [← alternate_normalizeTerms l,← alternate_normalizeTerms k,h]

end SlaterListCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_insert
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_collect
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.evalTerms_dropZero
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_removeRepeated
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_normalizeTerm
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_evalTerms_map
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_normalizeTerms
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_eq_of_normalizeTerms_eq
