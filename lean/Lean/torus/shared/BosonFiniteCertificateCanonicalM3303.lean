import torus.shared.BosonFiniteCertificateCanonicalRows303
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

 theorem k303_actual_channel0 :
    canonicalRowChannel k303occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((3-0).factorial : ℤ) •
        ((p303action0Raw)ᵀ * p303action0Raw - (p303pair0Raw)ᵀ * p303pair0Raw))) := by
  apply canonicalRowChannel_eq k303occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (3-0) (by omega)
    p303action0Raw p303pair0Raw
  · intro i a
    simpa only [p303action0Raw] using
      k303_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p303pair0Raw, threeRowAction_singleton] using
      k303_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k303_actual_channel0

 theorem k303_actual_channel1 :
    canonicalRowChannel k303occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((3-1).factorial : ℤ) •
        ((p303action1Raw)ᵀ * p303action1Raw - (p303pair1Raw)ᵀ * p303pair1Raw))) := by
  apply canonicalRowChannel_eq k303occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (3-1) (by omega)
    p303action1Raw p303pair1Raw
  · intro i a
    simpa only [p303action1Raw] using
      k303_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p303pair1Raw, threeRowAction_singleton] using
      k303_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k303_actual_channel1

 theorem k303_actual_channel2 :
    canonicalRowChannel k303occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 =
      complexify (integerForm (((3-2).factorial : ℤ) •
        ((p303action2Raw)ᵀ * p303action2Raw - (p303pair2Raw)ᵀ * p303pair2Raw))) := by
  apply canonicalRowChannel_eq k303occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 (3-2) (by omega)
    p303action2Raw p303pair2Raw
  · intro i a
    simpa only [p303action2Raw] using
      k303_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        ((frozenRows 2)[i.val]?.getD []) a
  · intro i a
    simpa only [p303pair2Raw, threeRowAction_singleton] using
      k303_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 2)[i.val]?.getD []) 0] a

#print axioms k303_actual_channel2

 theorem k303_actual_channel3 :
    canonicalRowChannel k303occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 =
      complexify (integerForm (((3-3).factorial : ℤ) •
        ((p303action3Raw)ᵀ * p303action3Raw - (p303pair3Raw)ᵀ * p303pair3Raw))) := by
  apply canonicalRowChannel_eq k303occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 (3-3) (by omega)
    p303action3Raw p303pair3Raw
  · intro i a
    simpa only [p303action3Raw] using
      k303_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        ((frozenRows 3)[i.val]?.getD []) a
  · intro i a
    simpa only [p303pair3Raw, threeRowAction_singleton] using
      k303_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 3)[i.val]?.getD []) 0] a

#print axioms k303_actual_channel3

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k303actualM3 : Matrix (Fin 3) (Fin 3) ℂ :=
  canonicalRowChannel k303occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k303occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 +
  canonicalRowChannel k303occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 +
  canonicalRowChannel k303occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3

theorem k303_actual_M3_raw : k303actualM3 = complexify p303rawMform := by
  unfold k303actualM3 p303rawMform p303rawNumerator
  rw [k303_actual_channel0, k303_actual_channel1, k303_actual_channel2, k303_actual_channel3]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k303_actual_M3_reconstructed : k303actualM3 = complexify p303Mform := by
  rw [k303_actual_M3_raw, p303_Mform_reconstructed]

#print axioms k303_actual_M3_raw
#print axioms k303_actual_M3_reconstructed

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k303_all_original_row_channels :
    canonicalAllRowChannels k303occ = k303actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k303occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k303occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k303occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k303occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k303actualM3
  simp only [add_zero, k303actualM3]

#print axioms k303_all_original_row_channels
end TorusLean.BosonFiniteCertificate
