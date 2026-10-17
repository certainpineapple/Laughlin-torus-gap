import torus.shared.BosonFiniteCertificateNatFourDegreeSparse

/-! A fully computable list evaluator, proved equal to the genuine source
form. Mathlib Finsupp support addition uses classical equality internally;
permutation and recursive count products avoid that implementation issue
without changing either the actual occupations or their physical metric. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem natFourOccupation_eq_iff_perm (s u : List ℕ) :
    wordOccupation s=wordOccupation u ↔ s.Perm u := by
  constructor
  · intro h
    apply List.perm_iff_count.mpr
    intro j
    simpa only [wordOccupation_apply] using congrArg (fun n : ℕ →₀ ℕ => n j) h
  · intro h
    apply Finsupp.ext
    intro j
    simpa only [wordOccupation_apply] using List.perm_iff_count.mp h j

/-- Each newly inserted occurrence contributes the current multiplicity.
For example [0,0,0,0] gives 4*3*2*1, not one. -/
def natFourMultiplicity : List ℕ → ℕ
  | [] => 1
  | j :: s => (s.count j+1)*natFourMultiplicity s

theorem natFourMultiplicity_eq_weight (s : List ℕ) :
    natFourMultiplicity s=natOccupationWeight (wordOccupation s) := by
  induction s with
  | nil => simp [natFourMultiplicity,natOccupationWeight,wordOccupation]
  | cons j s ih =>
    rw [natFourMultiplicity,ih,wordOccupation,add_comm (Finsupp.single j 1),
      natOccupationWeight_add_single,wordOccupation_apply]

def natFourComputableMetric (s : List ℕ) : ℕ :=
  natFourMultiplicity s*(s.map Nat.factorial).prod

theorem natFourComputableMetric_eq (s : List ℕ) :
    natFourComputableMetric s=natFourWordMetric s := by
  rw [natFourComputableMetric,natFourMultiplicity_eq_weight]
  rfl

def natFourComputableNormalForm (s u creators annihilators : List ℕ) : ℚ :=
  if s.Perm (creators++eraseWord u annihilators) then
    (wordRemovalWeight u annihilators : ℚ)*(natFourComputableMetric s : ℚ) else 0

theorem natFourComputableNormalForm_eq (s u creators annihilators : List ℕ) :
    natFourComputableNormalForm s u creators annihilators =
      natFourNormalWordForm s u creators annihilators := by
  simp only [natFourComputableNormalForm,natFourNormalWordForm,
    natFourOccupation_eq_iff_perm,natFourComputableMetric_eq]

def natFourComputableTermsForm (terms : List NatFourNormalTerm) (s u : List ℕ) : ℚ :=
  (terms.map fun term => if wordRemovalWeight u term.annihilators=0 then 0 else
    term.coefficient*natFourComputableNormalForm s u term.creators term.annihilators).sum

theorem natFourComputableTermsForm_eq (terms : List NatFourNormalTerm) (s u : List ℕ) :
    natFourComputableTermsForm terms s u=natFourTermsFormSparse terms s u := by
  simp only [natFourComputableTermsForm,natFourTermsFormSparse,natFourComputableNormalForm_eq]

def natFourComputableUnitForm (t : ℕ) (left right : Option (ℕ × ℕ)) (s u : List ℕ) : ℚ :=
  match left,right with
  | some (p,j),some (p',j') =>
      if (p+j-t)+j'+p'=u.sum then
        natFourComputableTermsForm (natFourColumnPairTerms t (left,1) (right,1)) s u else 0
  | _,_ => 0

theorem natFourComputableUnitForm_eq (t : ℕ) (left right : Option (ℕ × ℕ)) (s u : List ℕ) :
    natFourComputableUnitForm t left right s u=natFourDegreeUnitColumnForm t left right s u := by
  cases left <;> cases right <;>
    simp only [natFourComputableUnitForm,natFourDegreeUnitColumnForm,
      natFourComputableTermsForm_eq,natFourUnitColumnFormSparse]

def natFourComputableChannelForm (t : ℕ) (s u : List ℕ) : ℚ :=
  ((natFourColumnSlots t).map fun i => ((natFourColumnSlots t).map fun j =>
    let F := natFourComputableUnitForm t (natFourSourceColumn t i) (natFourSourceColumn t j) s u
    if F=0 then 0 else (natFourOriginalColumnGram t i j : ℚ)*F).sum).sum

theorem natFourComputableChannelForm_eq (t : ℕ) (s u : List ℕ) :
    natFourComputableChannelForm t s u=natFourDegreeChannelGramForm t s u := by
  simp only [natFourComputableChannelForm,natFourDegreeChannelGramForm,natFourComputableUnitForm_eq]

def natFourComputableGramForm (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t => natFourComputableChannelForm t s u).sum

theorem natFourComputableGramForm_eq (s u : List ℕ) :
    natFourComputableGramForm s u=natFourDegreeOriginalGramForm s u := by
  simp only [natFourComputableGramForm,natFourDegreeOriginalGramForm,natFourComputableChannelForm_eq]

theorem canonicalNatFourOriginalOperator_computable_form (s u : List ℕ) (hu : u.length=4) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourOriginalOperator (scaledWord factorialRootNat u)) =
      (natFourComputableGramForm s u : ℂ) := by
  rw [natFourComputableGramForm_eq,canonicalNatFourOriginalOperator_degree_form s u hu]

#print axioms natFourOccupation_eq_iff_perm
#print axioms natFourMultiplicity_eq_weight
#print axioms natFourComputableMetric_eq
#print axioms natFourComputableNormalForm_eq
#print axioms natFourComputableTermsForm_eq
#print axioms natFourComputableUnitForm_eq
#print axioms natFourComputableChannelForm_eq
#print axioms natFourComputableGramForm_eq
#print axioms canonicalNatFourOriginalOperator_computable_form
end TorusLean.BosonFiniteCertificate
