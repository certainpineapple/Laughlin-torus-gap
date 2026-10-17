import torus.shared.BosonFiniteCertificateCanonicalRows307
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

 theorem k307_actual_channel0 :
    canonicalRowChannel k307occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((7-0).factorial : ℤ) •
        ((p307action0Raw)ᵀ * p307action0Raw - (p307pair0Raw)ᵀ * p307pair0Raw))) := by
  apply canonicalRowChannel_eq k307occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (7-0) (by omega)
    p307action0Raw p307pair0Raw
  · intro i a
    simpa only [p307action0Raw] using
      k307_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p307pair0Raw, threeRowAction_singleton] using
      k307_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k307_actual_channel0

 theorem k307_actual_channel1 :
    canonicalRowChannel k307occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((7-1).factorial : ℤ) •
        ((p307action1Raw)ᵀ * p307action1Raw - (p307pair1Raw)ᵀ * p307pair1Raw))) := by
  apply canonicalRowChannel_eq k307occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (7-1) (by omega)
    p307action1Raw p307pair1Raw
  · intro i a
    simpa only [p307action1Raw] using
      k307_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p307pair1Raw, threeRowAction_singleton] using
      k307_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k307_actual_channel1

 theorem k307_actual_channel2 :
    canonicalRowChannel k307occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 =
      complexify (integerForm (((7-2).factorial : ℤ) •
        ((p307action2Raw)ᵀ * p307action2Raw - (p307pair2Raw)ᵀ * p307pair2Raw))) := by
  apply canonicalRowChannel_eq k307occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 (7-2) (by omega)
    p307action2Raw p307pair2Raw
  · intro i a
    simpa only [p307action2Raw] using
      k307_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        ((frozenRows 2)[i.val]?.getD []) a
  · intro i a
    simpa only [p307pair2Raw, threeRowAction_singleton] using
      k307_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 2)[i.val]?.getD []) 0] a

#print axioms k307_actual_channel2

 theorem k307_actual_channel3 :
    canonicalRowChannel k307occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 =
      complexify (integerForm (((7-3).factorial : ℤ) •
        ((p307action3Raw)ᵀ * p307action3Raw - (p307pair3Raw)ᵀ * p307pair3Raw))) := by
  apply canonicalRowChannel_eq k307occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 (7-3) (by omega)
    p307action3Raw p307pair3Raw
  · intro i a
    simpa only [p307action3Raw] using
      k307_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        ((frozenRows 3)[i.val]?.getD []) a
  · intro i a
    simpa only [p307pair3Raw, threeRowAction_singleton] using
      k307_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 3)[i.val]?.getD []) 0] a

#print axioms k307_actual_channel3

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k307actualM3 : Matrix (Fin 8) (Fin 8) ℂ :=
  canonicalRowChannel k307occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k307occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 +
  canonicalRowChannel k307occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 +
  canonicalRowChannel k307occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3

theorem k307_actual_M3_raw : k307actualM3 = complexify p307rawMform := by
  unfold k307actualM3 p307rawMform p307rawNumerator
  rw [k307_actual_channel0, k307_actual_channel1, k307_actual_channel2, k307_actual_channel3]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k307_actual_M3_reconstructed : k307actualM3 = complexify p307Mform := by
  rw [k307_actual_M3_raw, p307_Mform_reconstructed]

#print axioms k307_actual_M3_raw
#print axioms k307_actual_M3_reconstructed

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k307_all_original_row_channels :
    canonicalAllRowChannels k307occ = k307actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k307occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k307occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k307occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k307occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k307actualM3
  simp only [add_zero, k307actualM3]

#print axioms k307_all_original_row_channels
end TorusLean.BosonFiniteCertificate
