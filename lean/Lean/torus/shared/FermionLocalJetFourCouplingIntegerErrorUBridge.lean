import torus.shared.FermionLocalJetFourCouplingIntegerError
import torus.shared.FermionLocalJetFourCouplingSlaterListUBridge
import OAI.Analysis.Laughlin.FourBody.Basic

/- The actual seven-row ordered integer source is the original rational Y.
No finite table is used here. The coefficient bridge is a proved prerequisite,
not an additional hypothesis on the original comparison theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

theorem integerFourV_eq_originalV (D T r p j k : ℕ)
    (hDT : D ≤ T) (hT : p+j+k=T) :
    integerFourV D T r p j k = OAI.Laughlin.Certificate.V r D T p j k := by
  by_cases hr : r ≤ j+k
  · have hp : p ≤ T-r := by omega
    simp only [integerFourV,OAI.Laughlin.Certificate.V,if_pos hr]
    rw [SlaterListCandidate.integerS45Coefficient_eq_U r (j+k) j hr (by omega),
      SlaterListCandidate.integerS45Coefficient_eq_U (D-r) (T-r) p
        (Nat.sub_le_sub_right hDT r) hp]
  · simp only [integerFourV,OAI.Laughlin.Certificate.V,if_neg hr]

theorem integerFourRowEntry_eq_originalYEntry (D r s : ℕ)
    (rho : CertificateRow) (a b : CertificateEntry rho) :
    integerFourRowEntry D r s rho a b =
      OAI.Laughlin.Certificate.yEntry D r s (certificateRowData rho).1
        (certificateEntryData rho a) (certificateEntryData rho b) / (10^14 : ℚ) := by
  by_cases hDT : D ≤ certificateFourTotal rho a b
  · have hDT' : D ≤ (certificateEntryData rho a).1 +
        (certificateEntryData rho a).2.1 +
        ((certificateEntryData rho b).1 + (certificateEntryData rho b).2.1 -
          (certificateRowData rho).1) := by
      simpa only [certificateFourTotal,certificateJetIndex] using hDT
    have hVa := integerFourV_eq_originalV D (certificateFourTotal rho a b) r
      (certificateEntryData rho a).1 (certificateEntryData rho a).2.1
      (certificateJetIndex rho b) hDT rfl
    have hVb := integerFourV_eq_originalV D (certificateFourTotal rho a b) s
      (certificateEntryData rho b).1 (certificateEntryData rho b).2.1
      (certificateJetIndex rho a) hDT (certificateFourTotal_exchange rho b a)
    simp only [integerFourRowEntry,if_pos hDT,hVa,hVb]
    unfold OAI.Laughlin.Certificate.yEntry
    dsimp only
    rw [if_pos hDT']
    norm_num [certificateFourTotal,certificateJetIndex]
  · have hDT' : ¬ D ≤ (certificateEntryData rho a).1 +
        (certificateEntryData rho a).2.1 +
        ((certificateEntryData rho b).1 + (certificateEntryData rho b).2.1 -
          (certificateRowData rho).1) := by
      simpa only [certificateFourTotal,certificateJetIndex] using hDT
    simp only [integerFourRowEntry,if_neg hDT]
    unfold OAI.Laughlin.Certificate.yEntry
    dsimp only
    rw [if_neg hDT']
    norm_num

private theorem original_list_index_sum {α : Type*} (L : List α) (f : α → ℚ) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map L f)

theorem integerFourError_eq_originalY (D r s : ℕ) :
    integerFourError D r s = OAI.Laughlin.Certificate.Y D r s := by
  have hs :
      (∑ rho : CertificateRow, ∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
        OAI.Laughlin.Certificate.yEntry D r s (certificateRowData rho).1
          (certificateEntryData rho a) (certificateEntryData rho b)) =
      (OAI.Laughlin.Certificate.rows.map (OAI.Laughlin.Certificate.yRow D r s)).sum := by
    calc
      _ = ∑ rho : CertificateRow,
          OAI.Laughlin.Certificate.yRow D r s (certificateRowData rho) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        simp only [OAI.Laughlin.Certificate.yRow,certificateEntryData,CertificateEntry]
        simp_rw [original_list_index_sum]
        exact original_list_index_sum (certificateRowData rho).2.2
          (fun e => ((certificateRowData rho).2.2.map
            (fun f => OAI.Laughlin.Certificate.yEntry D r s
              (certificateRowData rho).1 e f)).sum)
      _ = _ := by
        change (∑ rho : Fin TorusLean.FermionM1.rows.length,
          OAI.Laughlin.Certificate.yRow D r s (TorusLean.FermionM1.rows.get rho)) = _
        rw [original_list_index_sum]
        rfl
  unfold integerFourError OAI.Laughlin.Certificate.Y
  simp_rw [integerFourRowEntry_eq_originalYEntry]
  simp only [← Finset.sum_div]
  rw [hs]
  ring

theorem integerFourErrorMatrix_eq_originalY (D : ℕ) :
    integerFourErrorMatrix D = OAI.Laughlin.Certificate.errorRational D := by
  ext i j
  exact integerFourError_eq_originalY D (2*i.val+1) (2*j.val+1)

#print axioms integerFourV_eq_originalV
#print axioms integerFourRowEntry_eq_originalYEntry
#print axioms integerFourError_eq_originalY
#print axioms integerFourErrorMatrix_eq_originalY
end TorusLean.Shared.FermionLocalJet.FourCoupling
