import torus.shared.BosonFiniteCertificateCanonicalRows304
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

 theorem k304_actual_channel0 :
    canonicalRowChannel k304occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((4-0).factorial : ℤ) •
        ((p304action0Raw)ᵀ * p304action0Raw - (p304pair0Raw)ᵀ * p304pair0Raw))) := by
  apply canonicalRowChannel_eq k304occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (4-0) (by omega)
    p304action0Raw p304pair0Raw
  · intro i a
    simpa only [p304action0Raw] using
      k304_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p304pair0Raw, threeRowAction_singleton] using
      k304_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k304_actual_channel0

 theorem k304_actual_channel1 :
    canonicalRowChannel k304occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((4-1).factorial : ℤ) •
        ((p304action1Raw)ᵀ * p304action1Raw - (p304pair1Raw)ᵀ * p304pair1Raw))) := by
  apply canonicalRowChannel_eq k304occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (4-1) (by omega)
    p304action1Raw p304pair1Raw
  · intro i a
    simpa only [p304action1Raw] using
      k304_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p304pair1Raw, threeRowAction_singleton] using
      k304_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k304_actual_channel1

 theorem k304_actual_channel2 :
    canonicalRowChannel k304occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 =
      complexify (integerForm (((4-2).factorial : ℤ) •
        ((p304action2Raw)ᵀ * p304action2Raw - (p304pair2Raw)ᵀ * p304pair2Raw))) := by
  apply canonicalRowChannel_eq k304occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 (4-2) (by omega)
    p304action2Raw p304pair2Raw
  · intro i a
    simpa only [p304action2Raw] using
      k304_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        ((frozenRows 2)[i.val]?.getD []) a
  · intro i a
    simpa only [p304pair2Raw, threeRowAction_singleton] using
      k304_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 2)[i.val]?.getD []) 0] a

#print axioms k304_actual_channel2

 theorem k304_actual_channel3 :
    canonicalRowChannel k304occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 =
      complexify (integerForm (((4-3).factorial : ℤ) •
        ((p304action3Raw)ᵀ * p304action3Raw - (p304pair3Raw)ᵀ * p304pair3Raw))) := by
  apply canonicalRowChannel_eq k304occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 (4-3) (by omega)
    p304action3Raw p304pair3Raw
  · intro i a
    simpa only [p304action3Raw] using
      k304_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        ((frozenRows 3)[i.val]?.getD []) a
  · intro i a
    simpa only [p304pair3Raw, threeRowAction_singleton] using
      k304_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 3)[i.val]?.getD []) 0] a

#print axioms k304_actual_channel3

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k304actualM3 : Matrix (Fin 4) (Fin 4) ℂ :=
  canonicalRowChannel k304occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k304occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 +
  canonicalRowChannel k304occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 +
  canonicalRowChannel k304occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3

theorem k304_actual_M3_raw : k304actualM3 = complexify p304rawMform := by
  unfold k304actualM3 p304rawMform p304rawNumerator
  rw [k304_actual_channel0, k304_actual_channel1, k304_actual_channel2, k304_actual_channel3]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k304_actual_M3_reconstructed : k304actualM3 = complexify p304Mform := by
  rw [k304_actual_M3_raw, p304_Mform_reconstructed]

#print axioms k304_actual_M3_raw
#print axioms k304_actual_M3_reconstructed

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k304_all_original_row_channels :
    canonicalAllRowChannels k304occ = k304actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k304occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k304occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k304occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k304occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k304actualM3
  simp only [add_zero, k304actualM3]

#print axioms k304_all_original_row_channels
end TorusLean.BosonFiniteCertificate
