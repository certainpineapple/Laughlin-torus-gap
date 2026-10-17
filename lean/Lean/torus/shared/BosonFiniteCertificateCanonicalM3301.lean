import torus.shared.BosonFiniteCertificateCanonicalRows301
import torus.shared.BosonFiniteCertificateCanonicalRowAssembly
import torus.shared.BosonFiniteCertificateCanonicalZeroChannels
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate

 theorem k301_actual_channel0 :
    canonicalRowChannel k301occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((1-0).factorial : ℤ) •
        ((p301action0Raw)ᵀ * p301action0Raw - (p301pair0Raw)ᵀ * p301pair0Raw))) := by
  apply canonicalRowChannel_eq k301occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (1-0) (by omega)
    p301action0Raw p301pair0Raw
  · intro i a
    simpa only [p301action0Raw] using
      k301_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p301pair0Raw, threeRowAction_singleton] using
      k301_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k301_actual_channel0

 theorem k301_actual_channel1 :
    canonicalRowChannel k301occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((1-1).factorial : ℤ) •
        ((p301action1Raw)ᵀ * p301action1Raw - (p301pair1Raw)ᵀ * p301pair1Raw))) := by
  apply canonicalRowChannel_eq k301occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (1-1) (by omega)
    p301action1Raw p301pair1Raw
  · intro i a
    simpa only [p301action1Raw] using
      k301_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p301pair1Raw, threeRowAction_singleton] using
      k301_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k301_actual_channel1

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k301actualM3 : Matrix (Fin 1) (Fin 1) ℂ :=
  canonicalRowChannel k301occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k301occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1

theorem k301_actual_M3_raw : k301actualM3 = complexify p301rawMform := by
  unfold k301actualM3 p301rawMform p301rawNumerator
  rw [k301_actual_channel0, k301_actual_channel1]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k301_actual_M3_reconstructed : k301actualM3 = complexify p301Mform := by
  rw [k301_actual_M3_raw, p301_Mform_reconstructed]

#print axioms k301_actual_M3_raw
#print axioms k301_actual_M3_reconstructed

theorem k301_missing_channel2 : canonicalRowChannel k301occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 = 0 := by
  apply canonicalRowChannel_zero
  intro row a
  rw [k301_actual_canonical_row (⟨2, by decide⟩ : Fin 4) row a]
  have hs : (p301basis a).sum = 1 := by fin_cases a <;> decide +kernel
  rw [threeRowAction_zero_above_degree (⟨2, by decide⟩ : Fin 4) row
    (p301basis a) (by simp only [Fin.val_mk]; omega)]
  simp

#print axioms k301_missing_channel2

theorem k301_missing_channel3 : canonicalRowChannel k301occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 = 0 := by
  apply canonicalRowChannel_zero
  intro row a
  rw [k301_actual_canonical_row (⟨3, by decide⟩ : Fin 4) row a]
  have hs : (p301basis a).sum = 1 := by fin_cases a <;> decide +kernel
  rw [threeRowAction_zero_above_degree (⟨3, by decide⟩ : Fin 4) row
    (p301basis a) (by simp only [Fin.val_mk]; omega)]
  simp

#print axioms k301_missing_channel3

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k301_all_original_row_channels :
    canonicalAllRowChannels k301occ = k301actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k301occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k301occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k301occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k301occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k301actualM3
  rw [k301_missing_channel2, k301_missing_channel3]
  simp only [add_zero, k301actualM3]

#print axioms k301_all_original_row_channels
end TorusLean.BosonFiniteCertificate
