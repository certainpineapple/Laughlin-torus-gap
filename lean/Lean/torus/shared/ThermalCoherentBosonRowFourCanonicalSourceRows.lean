import torus.shared.ThermalCoherentBosonRowFourCanonicalSourceColumn
import torus.shared.ThermalCoherentBosonRowSource

/-! The original 138 row/column lists are reindexed without removing zero
or repeated rows. Their literal four-body rank form is grouped by the two
original created labels, using only the already fixed Y_i source. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

private theorem zip_ofFn {A B : Type*} (l : List A) (r : List B)
    (h : l.length=r.length) : l.zip r = List.ofFn (fun a : Fin l.length =>
      (l.get a,r.get ⟨a.val,by rw [← h]; exact a.isLt⟩)) := by
  apply List.ext_getElem
  · simp [h]
  · intro n hn hm
    simp only [List.getElem_zip,List.getElem_ofFn,List.get_eq_getElem]

/-- Exact original zip, including its pure-pair head and every spectator slot. -/
theorem fourCanonical_source_zip (ρ : RowIndex) :
    (columns ρ.1.val).zip (rowData ρ) =
      (none,rowInteger (rowData ρ) 0) :: List.ofFn (fun a : EntryIndex ρ =>
        (some (entryPair ρ a),entryInteger ρ a)) := by
  have hc : columns ρ.1.val=none :: (columns ρ.1.val).tail := rfl
  have hh : (columns ρ.1.val).zip (rowData ρ) =
      (none,rowInteger (rowData ρ) 0) ::
        ((columns ρ.1.val).tail.zip (rowData ρ).tail) := by
    rw [hc]
    cases hr : rowData ρ with
    | nil =>
      have h := rowData_length ρ
      rw [hr,hc] at h
      simp at h
    | cons c rest => simp [rowInteger]
  rw [hh]
  congr 1
  have hl : (columns ρ.1.val).tail.length=(rowData ρ).tail.length := by
    simp only [List.length_tail,rowData_length]
  rw [zip_ofFn _ _ hl]
  apply congrArg List.ofFn
  funext a
  apply Prod.ext
  · exact (entry_support ρ a).1
  · have ha : a.val+1<(rowData ρ).length := by
      have hb := a.isLt.trans_le (le_of_eq hl)
      have ht : (rowData ρ).tail.length=(rowData ρ).length-1 := List.length_tail
      omega
    simp only [entryInteger,rowInteger,List.get_eq_getElem,List.getElem_tail,
      List.getElem?_eq_getElem ha,Option.getD_some]

def fourCanonicalEntryCross (ρ : RowIndex) (a b : EntryIndex ρ)
    (f g : Core ℕ ℂ) : ℂ :=
  (rowAlpha ρ a:ℂ)*(rowAlpha ρ b:ℂ)*
    star (natOccupationInner
      ((pairCOMSeed (entryPair ρ a).1*MvPolynomial.X (entryPair ρ a).2)*
        MvPolynomial.X (entryJet ρ b)) f) *
    natOccupationInner
      ((pairCOMSeed (entryPair ρ b).1*MvPolynomial.X (entryPair ρ b).2)*
        MvPolynomial.X (entryJet ρ a)) g

private theorem column_none_left (t : ℕ) (c : ℤ) (right : Option (ℕ × ℕ) × ℤ)
    (f g : Core ℕ ℂ) :
    ((natFourColumnPairTerms t (none,c) right).map (fourCanonicalRankTerm f g)).sum=0 := by
  cases right.1 <;> rfl

private theorem column_none_right (t : ℕ) (c : ℤ) (left : Option (ℕ × ℕ) × ℤ)
    (f g : Core ℕ ℂ) :
    ((natFourColumnPairTerms t left (none,c)).map (fourCanonicalRankTerm f g)).sum=0 := by
  rcases left with ⟨left,c'⟩
  cases left <;> rfl

/-- Each original row's literal normal tensor is its decoded column-pair sum. -/
theorem fourCanonical_original_row_cross (ρ : RowIndex) (f g : Core ℕ ℂ) :
    ((natFourOriginalRowTerms ρ.1.val (rowData ρ)).map
      (fourCanonicalRankTerm f g)).sum =
      ∑ a : EntryIndex ρ, ∑ b : EntryIndex ρ, fourCanonicalEntryCross ρ a b f g := by
  simp only [natFourOriginalRowTerms,fourCanonical_source_zip,fourCanonical_terms_flatMap,
    List.map_cons,List.sum_cons,List.map_ofFn,Fin.sum_ofFn,Function.comp_def,
    column_none_left,column_none_right,Finset.sum_const_zero,zero_add,add_zero]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact fourCanonical_column_pair_cross ρ.1.val
    (entryPair ρ a).1 (entryPair ρ a).2 (entryPair ρ b).1 (entryPair ρ b).2
    (entryInteger ρ a) (entryInteger ρ b) f g

private theorem fiber_sum {A : Type*} [Fintype A] (r : A → Fin 9) (F : A → ℂ) :
    (∑ i : Fin 9, ∑ a ∈ Finset.univ.filter (fun a => r a=i), F a) = ∑ a, F a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

/-- Grouping creates exactly the crossed Y_i X_j sources, with no multiplicity
factor. The labels stay in the original full nine-label spectator family. -/
theorem fourCanonical_grouped_cross (ρ : RowIndex) (f g : Core ℕ ℂ) :
    (∑ i : Fin 9, ∑ j : Fin 9,
      star (natOccupationInner (rowThreeAuxiliarySeed ρ i*MvPolynomial.X j.val) f) *
        natOccupationInner (rowThreeAuxiliarySeed ρ j*MvPolynomial.X i.val) g) =
      ∑ a : EntryIndex ρ, ∑ b : EntryIndex ρ, fourCanonicalEntryCross ρ a b f g := by
  have h : (∑ i : Fin 9, ∑ j : Fin 9,
      star (natOccupationInner (rowThreeAuxiliarySeed ρ i*MvPolynomial.X j.val) f) *
        natOccupationInner (rowThreeAuxiliarySeed ρ j*MvPolynomial.X i.val) g) =
      ∑ i : Fin 9, ∑ j : Fin 9,
        ∑ a ∈ Finset.univ.filter (fun a => entryJetFin ρ a=i),
          ∑ b ∈ Finset.univ.filter (fun b => entryJetFin ρ b=j),
            fourCanonicalEntryCross ρ a b f g := by
    simp only [rowThreeAuxiliarySeed,Finset.sum_mul,smul_mul_assoc,
      natOccupationInner_sum_left,natOccupationInner_smul_left,star_sum,star_mul,
      star_star,Complex.star_def,Complex.conj_ofReal,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have ha' := congrArg Fin.val (Finset.mem_filter.mp ha).2
    have hb' := congrArg Fin.val (Finset.mem_filter.mp hb).2
    change entryJet ρ a=i.val at ha'
    change entryJet ρ b=j.val at hb'
    simp only [fourCanonicalEntryCross,ha',hb',Complex.star_def]
    ring
  rw [h]
  calc
    _ = ∑ i : Fin 9, ∑ a ∈ Finset.univ.filter (fun a => entryJetFin ρ a=i),
        ∑ j : Fin 9, ∑ b ∈ Finset.univ.filter (fun b => entryJetFin ρ b=j),
          fourCanonicalEntryCross ρ a b f g := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [fiber_sum]

private theorem list_sum_get {A : Type*} (l : List A) (F : A → ℂ) :
    (l.map F).sum = ∑ r : Fin l.length, F (l.get r) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn,Fin.sum_ofFn]
  rfl

/-- Every original row occurs once, before any finite-mode or COM comparison. -/
theorem fourCanonical_original_terms_cross (f g : Core ℕ ℂ) :
    (natFourOriginalTerms.map (fourCanonicalRankTerm f g)).sum =
      ∑ ρ : RowIndex, ∑ i : Fin 9, ∑ j : Fin 9,
        star (natOccupationInner (rowThreeAuxiliarySeed ρ i*MvPolynomial.X j.val) f) *
          natOccupationInner (rowThreeAuxiliarySeed ρ j*MvPolynomial.X i.val) g := by
  simp only [natFourOriginalTerms,natFourOriginalRows,List.flatMap_assoc,
    List.flatMap_map,Function.comp_def,fourCanonical_terms_flatMap]
  rw [Fintype.sum_sigma,list_sum_get (List.range 4)]
  simp only [List.get_eq_getElem,List.getElem_range]
  change (∑ t : Fin 4, ((frozenRows t.val).map (fun row =>
    ((natFourOriginalRowTerms t.val row).map (fourCanonicalRankTerm f g)).sum)).sum) = _
  apply Finset.sum_congr rfl
  intro t _
  rw [list_sum_get (frozenRows t.val)]
  apply Finset.sum_congr rfl
  intro r _
  change ((natFourOriginalRowTerms t.val (rowData ⟨t,r⟩)).map
    (fourCanonicalRankTerm f g)).sum = _
  exact (fourCanonical_original_row_cross ⟨t,r⟩ f g).trans
    (fourCanonical_grouped_cross ⟨t,r⟩ f g).symm

#print axioms fourCanonical_source_zip
#print axioms fourCanonical_original_row_cross
#print axioms fourCanonical_grouped_cross
#print axioms fourCanonical_original_terms_cross
end TorusLean.Shared.ThermalCoherentBosonRows
