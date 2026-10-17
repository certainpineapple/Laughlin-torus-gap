import torus.shared.FermionLocalJetFourCouplingSlaterListSource

/-! The same proved integer presentation, with zero terms removed BEFORE the
sorting/merging pass. This improves evaluation only and preserves every source
mode. It neither modifies original definitions nor narrows an original target. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
namespace SlaterListCandidate

def normalizeTermsFast (l : List Term) : List Term :=
  dropZero (collectTerms (dropZero ((dropZero l).map normalizeTerm)))

theorem alternate_normalizeTermsFast (l : List Term) :
    alternateIntegerFourWords (evalTerms (normalizeTermsFast l))=
      alternateIntegerFourWords (evalTerms l) := by
  rw [normalizeTermsFast,evalTerms_dropZero,evalTerms_collect,evalTerms_dropZero,
    alternate_evalTerms_map,evalTerms_dropZero]

theorem alternate_eq_of_normalizeTermsFast_eq (l k : List Term)
    (h : normalizeTermsFast l=normalizeTermsFast k) :
    alternateIntegerFourWords (evalTerms l)=alternateIntegerFourWords (evalTerms k) := by
  rw [← alternate_normalizeTermsFast l,← alternate_normalizeTermsFast k,h]

theorem originalSlaterSource_of_fast_list_check (D : ℕ)
    (hcheck : ∀ r : OddMode D, normalizeTermsFast (sourceTerms D D r.val.val)=
      normalizeTermsFast (slaterTerms D r.val.val)) :
    ∀ r : OddMode D, alternateIntegerFourWords (integerSourceWords D D r.val.val)=
      alternateIntegerFourWords (integerSlaterWords D r.val.val) := by
  intro r
  rw [← sourceTerms_eval D D r.val.val (Nat.le_of_lt_succ r.val.isLt) le_rfl,
    ← slaterTerms_eval D r.val.val]
  exact alternate_eq_of_normalizeTermsFast_eq _ _ (hcheck r)

end SlaterListCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_normalizeTermsFast
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.alternate_eq_of_normalizeTermsFast_eq
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.originalSlaterSource_of_fast_list_check
