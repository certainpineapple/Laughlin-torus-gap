import torus.shared.BosonFiniteCertificateCanonicalRows300
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

 theorem k300_actual_channel0 :
    canonicalRowChannel k300occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((0-0).factorial : ℤ) •
        ((p300action0Raw)ᵀ * p300action0Raw - (p300pair0Raw)ᵀ * p300pair0Raw))) := by
  apply canonicalRowChannel_eq k300occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (0-0) (by omega)
    p300action0Raw p300pair0Raw
  · intro i a
    simpa only [p300action0Raw] using
      k300_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p300pair0Raw, threeRowAction_singleton] using
      k300_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k300_actual_channel0

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k300actualM3 : Matrix (Fin 1) (Fin 1) ℂ :=
  canonicalRowChannel k300occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0

theorem k300_actual_M3_raw : k300actualM3 = complexify p300rawMform := by
  unfold k300actualM3 p300rawMform p300rawNumerator
  rw [k300_actual_channel0]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k300_actual_M3_reconstructed : k300actualM3 = complexify p300Mform := by
  rw [k300_actual_M3_raw, p300_Mform_reconstructed]

#print axioms k300_actual_M3_raw
#print axioms k300_actual_M3_reconstructed

theorem k300_missing_channel1 : canonicalRowChannel k300occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 = 0 := by
  apply canonicalRowChannel_zero
  intro row a
  rw [k300_actual_canonical_row (⟨1, by decide⟩ : Fin 4) row a]
  have hs : (p300basis a).sum = 0 := by fin_cases a <;> decide +kernel
  rw [threeRowAction_zero_above_degree (⟨1, by decide⟩ : Fin 4) row
    (p300basis a) (by simp only [Fin.val_mk]; omega)]
  simp

#print axioms k300_missing_channel1

theorem k300_missing_channel2 : canonicalRowChannel k300occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 = 0 := by
  apply canonicalRowChannel_zero
  intro row a
  rw [k300_actual_canonical_row (⟨2, by decide⟩ : Fin 4) row a]
  have hs : (p300basis a).sum = 0 := by fin_cases a <;> decide +kernel
  rw [threeRowAction_zero_above_degree (⟨2, by decide⟩ : Fin 4) row
    (p300basis a) (by simp only [Fin.val_mk]; omega)]
  simp

#print axioms k300_missing_channel2

theorem k300_missing_channel3 : canonicalRowChannel k300occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 = 0 := by
  apply canonicalRowChannel_zero
  intro row a
  rw [k300_actual_canonical_row (⟨3, by decide⟩ : Fin 4) row a]
  have hs : (p300basis a).sum = 0 := by fin_cases a <;> decide +kernel
  rw [threeRowAction_zero_above_degree (⟨3, by decide⟩ : Fin 4) row
    (p300basis a) (by simp only [Fin.val_mk]; omega)]
  simp

#print axioms k300_missing_channel3

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k300_all_original_row_channels :
    canonicalAllRowChannels k300occ = k300actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k300occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k300occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k300occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k300occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k300actualM3
  rw [k300_missing_channel1, k300_missing_channel2, k300_missing_channel3]
  simp only [add_zero, k300actualM3]

#print axioms k300_all_original_row_channels
end TorusLean.BosonFiniteCertificate
