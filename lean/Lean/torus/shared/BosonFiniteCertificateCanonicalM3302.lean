import torus.shared.BosonFiniteCertificateCanonicalRows302
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

 theorem k302_actual_channel0 :
    canonicalRowChannel k302occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((2-0).factorial : ℤ) •
        ((p302action0Raw)ᵀ * p302action0Raw - (p302pair0Raw)ᵀ * p302pair0Raw))) := by
  apply canonicalRowChannel_eq k302occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (2-0) (by omega)
    p302action0Raw p302pair0Raw
  · intro i a
    simpa only [p302action0Raw] using
      k302_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p302pair0Raw, threeRowAction_singleton] using
      k302_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k302_actual_channel0

 theorem k302_actual_channel1 :
    canonicalRowChannel k302occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((2-1).factorial : ℤ) •
        ((p302action1Raw)ᵀ * p302action1Raw - (p302pair1Raw)ᵀ * p302pair1Raw))) := by
  apply canonicalRowChannel_eq k302occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (2-1) (by omega)
    p302action1Raw p302pair1Raw
  · intro i a
    simpa only [p302action1Raw] using
      k302_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p302pair1Raw, threeRowAction_singleton] using
      k302_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k302_actual_channel1

 theorem k302_actual_channel2 :
    canonicalRowChannel k302occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 =
      complexify (integerForm (((2-2).factorial : ℤ) •
        ((p302action2Raw)ᵀ * p302action2Raw - (p302pair2Raw)ᵀ * p302pair2Raw))) := by
  apply canonicalRowChannel_eq k302occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 (2-2) (by omega)
    p302action2Raw p302pair2Raw
  · intro i a
    simpa only [p302action2Raw] using
      k302_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        ((frozenRows 2)[i.val]?.getD []) a
  · intro i a
    simpa only [p302pair2Raw, threeRowAction_singleton] using
      k302_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 2)[i.val]?.getD []) 0] a

#print axioms k302_actual_channel2

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k302actualM3 : Matrix (Fin 2) (Fin 2) ℂ :=
  canonicalRowChannel k302occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k302occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 +
  canonicalRowChannel k302occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2

theorem k302_actual_M3_raw : k302actualM3 = complexify p302rawMform := by
  unfold k302actualM3 p302rawMform p302rawNumerator
  rw [k302_actual_channel0, k302_actual_channel1, k302_actual_channel2]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k302_actual_M3_reconstructed : k302actualM3 = complexify p302Mform := by
  rw [k302_actual_M3_raw, p302_Mform_reconstructed]

#print axioms k302_actual_M3_raw
#print axioms k302_actual_M3_reconstructed

theorem k302_missing_channel3 : canonicalRowChannel k302occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 = 0 := by
  apply canonicalRowChannel_zero
  intro row a
  rw [k302_actual_canonical_row (⟨3, by decide⟩ : Fin 4) row a]
  have hs : (p302basis a).sum = 2 := by fin_cases a <;> decide +kernel
  rw [threeRowAction_zero_above_degree (⟨3, by decide⟩ : Fin 4) row
    (p302basis a) (by simp only [Fin.val_mk]; omega)]
  simp

#print axioms k302_missing_channel3

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k302_all_original_row_channels :
    canonicalAllRowChannels k302occ = k302actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k302occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k302occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k302occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k302occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k302actualM3
  rw [k302_missing_channel3]
  simp only [add_zero, k302actualM3]

#print axioms k302_all_original_row_channels
end TorusLean.BosonFiniteCertificate
