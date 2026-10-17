import torus.shared.ThermalCoherentBosonRowCanonicalCCR
import torus.shared.ThermalCoherentBosonRowSource
import torus.shared.BosonFiniteCertificateNatRowForms

/-! The original M3 form is the three rank-cross terms of the original T_i/Y_i
sources, on the genuine particle-three Nat core. T and Y are imported from the
physical-source file rather than redefined here. High t+i fibers are removed
because Y_i is zero; no assertion that every T_i has degree at most eight is used. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

private theorem vacuum_cross (c d : ℂ) :
    natOccupationInner (c • (1 : Core ℕ ℂ)) (d • (1 : Core ℕ ℂ)) = star c*d := by
  have h11 : natOccupationInner (1 : Core ℕ ℂ) 1=1 := by
    change natOccupationInner (MvPolynomial.monomial 0 1) 1=1
    rw [natOccupationInner_monomial_left]
    simp [natOccupationWeight,Finsupp.prod]
  rw [natOccupationInner_smul_left,natOccupationInner_smul_right,h11,mul_one]

private theorem creator_fiber (ρ : RowIndex) (i : Fin 9) :
    Finset.univ.filter (fun a : EntryIndex ρ => entryJet ρ a=i.val) =
      Finset.univ.filter (fun a : EntryIndex ρ => entryJetFin ρ a=i) := by
  apply Finset.filter_congr
  intro a _
  change (entryJetFin ρ a).val=i.val ↔ entryJetFin ρ a=i
  exact Fin.ext_iff.symm

/-- The original pair test source, with its real λ and its original κ. -/
theorem canonicalRowPair_vacuum (ρ : RowIndex) (i : Fin 9)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) :
    annihilate i.val (canonicalRowPair ρ f) =
      natOccupationInner (rowThreePairSeed ρ i) f • (1 : Core ℕ ℂ) := by
  change annihilate i.val ((rowLambda ρ:ℂ) •
    ((natPairNormalization ρ.1.val • canonicalPairNat ρ.1.val) f)) = _
  rw [map_smul]
  change (rowLambda ρ:ℂ) • canonicalPairSpectator ρ.1.val i.val f = _
  rw [canonicalPairSpectator_vacuum _ _ f hN]
  simp only [rowThreePairSeed,natOccupationInner_smul_left,
    Complex.star_def,Complex.conj_ofReal,smul_smul]

/-- The unique physical Y_i source is the exact vacuum coefficient of the
original grouped canonical annihilator; all spectator columns are retained. -/
theorem canonicalRowGrouped_vacuum (ρ : RowIndex) (i : Fin 9)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) :
    canonicalRowGrouped ρ i f =
      natOccupationInner (rowThreeAuxiliarySeed ρ i) f • (1 : Core ℕ ℂ) := by
  simp only [canonicalRowGrouped,LinearMap.sum_apply,LinearMap.smul_apply]
  rw [creator_fiber]
  simp_rw [canonicalPairSpectator_vacuum _ _ f hN]
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  simp only [rowThreeAuxiliarySeed,natOccupationInner_sum_left,
    natOccupationInner_smul_left,Complex.star_def,Complex.conj_ofReal]

/-- The apparent four-body canonical remainder really vanishes on N3. -/
theorem canonicalRowGrouped_four_zero (ρ : RowIndex) (i : Fin 9) (j : ℕ)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) :
    annihilate j (canonicalRowGrouped ρ i f)=0 := by
  rw [canonicalRowGrouped_vacuum ρ i f hN,map_smul]
  change natOccupationInner (rowThreeAuxiliarySeed ρ i) f •
    MvPolynomial.pderiv j (1 : Core ℕ ℂ)=0
  rw [MvPolynomial.pderiv_one,smul_zero]

/-- Empty high-degree creator fibers give zero operators on the whole core. -/
theorem canonicalRowGrouped_above_degree (ρ : RowIndex) (i : Fin 9)
    (hi : 8<ρ.1.val+i.val) : canonicalRowGrouped ρ i=0 := by
  unfold canonicalRowGrouped
  apply Finset.sum_eq_zero
  intro a ha
  have hv := (Finset.mem_filter.mp ha).2
  have hs := entry_support ρ a
  have hlo := hs.2.2.2.1
  have hhi := hs.2.2.2.2.1
  unfold entryJet at hv
  omega

/-- The subtracted source in the original M3 definition is exactly its own
pure-pair column, not a newly chosen two-body operator. -/
theorem canonicalNatRow_pure_pair (ρ : RowIndex) :
    canonicalNatRow ρ.1.val [rowInteger (rowData ρ) 0] = canonicalRowPair ρ := by
  rw [canonicalNatRow_decoded_zip]
  simp [columns,decodedCanonicalColumn,canonicalRowPair,rowLambda]

def natRankSourceCross (u v f g : Core ℕ ℂ) : ℂ :=
  star (natOccupationInner u f)*natOccupationInner v g

def rowRankThreeForm (ρ : RowIndex) (f g : Core ℕ ℂ) : ℂ :=
  (∑ i : Fin 9, natRankSourceCross (rowThreePairSeed ρ i) (rowThreeAuxiliarySeed ρ i) f g) +
  (∑ i : Fin 9, natRankSourceCross (rowThreeAuxiliarySeed ρ i) (rowThreePairSeed ρ i) f g) +
  (∑ i : Fin 9, natRankSourceCross (rowThreeAuxiliarySeed ρ i) (rowThreeAuxiliarySeed ρ i) f g)

/-- Only the Y_i support is used here; the unused T_i may have degree >8. -/
theorem rowRankThreeTerm_above_degree (ρ : RowIndex) (i : Fin 9)
    (hi : 8<ρ.1.val+i.val) (f g : Core ℕ ℂ) :
    natRankSourceCross (rowThreePairSeed ρ i) (rowThreeAuxiliarySeed ρ i) f g +
      natRankSourceCross (rowThreeAuxiliarySeed ρ i) (rowThreePairSeed ρ i) f g +
      natRankSourceCross (rowThreeAuxiliarySeed ρ i) (rowThreeAuxiliarySeed ρ i) f g = 0 := by
  rw [rowThreeAuxiliarySeed_above_degree ρ i hi]
  simp only [natRankSourceCross,natOccupationInner_zero_left,star_zero,
    zero_mul,mul_zero,add_zero]

theorem rowRankThreeForm_cutoff (ρ : RowIndex) (f g : Core ℕ ℂ) :
    rowRankThreeForm ρ f g =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 9 => ρ.1.val+i.val≤8),
        (natRankSourceCross (rowThreePairSeed ρ i) (rowThreeAuxiliarySeed ρ i) f g +
         natRankSourceCross (rowThreeAuxiliarySeed ρ i) (rowThreePairSeed ρ i) f g +
         natRankSourceCross (rowThreeAuxiliarySeed ρ i) (rowThreeAuxiliarySeed ρ i) f g) := by
  unfold rowRankThreeForm
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ρ.1.val+i.val≤8
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact rowRankThreeTerm_above_degree ρ i (Nat.lt_of_not_ge hi) f g

/-- The genuine original row-square difference, on every N3 polynomial. -/
theorem canonicalNatRow_N3_rank_source (ρ : RowIndex) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    natOccupationInner (canonicalNatRow ρ.1.val (rowData ρ) f)
      (canonicalNatRow ρ.1.val (rowData ρ) g) -
      natOccupationInner (canonicalRowPair ρ f) (canonicalRowPair ρ g) =
        rowRankThreeForm ρ f g := by
  have h := canonicalNatRow_cross_normal_order ρ f g
  have hz (i j : Fin 9) := canonicalRowGrouped_four_zero ρ i j.val f hNf
  simp_rw [hz,natOccupationInner_zero_left] at h
  simp only [Finset.sum_const_zero,add_zero] at h
  simp_rw [canonicalRowPair_vacuum ρ _ f hNf,canonicalRowPair_vacuum ρ _ g hNg,
    canonicalRowGrouped_vacuum ρ _ f hNf,canonicalRowGrouped_vacuum ρ _ g hNg,
    vacuum_cross] at h
  unfold rowRankThreeForm natRankSourceCross
  linear_combination h

/-- All original 138 indices, including zero and repeated rows, give the exact
original M3 form. This is an identity on the actual particle-three core. -/
theorem canonicalNatOriginalM3Form_rank_source (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    canonicalNatOriginalM3Form f g = ∑ ρ : RowIndex, rowRankThreeForm ρ f g := by
  unfold canonicalNatOriginalM3Form canonicalNatRowChannelForm
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  rw [frozenRowCount_actual t]
  apply Finset.sum_congr rfl
  intro r _
  have hr : (frozenRows t.val)[r.val]?.getD [] = rowData ⟨t,r⟩ := by
    simp only [rowData,List.get_eq_getElem,List.getElem?_eq_getElem r.isLt,Option.getD_some]
  dsimp only
  rw [hr,canonicalNatRow_pure_pair ⟨t,r⟩]
  exact canonicalNatRow_N3_rank_source ⟨t,r⟩ f g hNf hNg

#print axioms canonicalRowPair_vacuum
#print axioms canonicalRowGrouped_vacuum
#print axioms canonicalRowGrouped_four_zero
#print axioms canonicalRowGrouped_above_degree
#print axioms canonicalNatRow_pure_pair
#print axioms rowRankThreeTerm_above_degree
#print axioms rowRankThreeForm_cutoff
#print axioms canonicalNatRow_N3_rank_source
#print axioms canonicalNatOriginalM3Form_rank_source
end TorusLean.Shared.ThermalCoherentBosonRows
