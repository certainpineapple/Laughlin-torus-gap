import torus.shared.BosonFiniteCertificateCanonicalRows305
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

 theorem k305_actual_channel0 :
    canonicalRowChannel k305occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((5-0).factorial : ℤ) •
        ((p305action0Raw)ᵀ * p305action0Raw - (p305pair0Raw)ᵀ * p305pair0Raw))) := by
  apply canonicalRowChannel_eq k305occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (5-0) (by omega)
    p305action0Raw p305pair0Raw
  · intro i a
    simpa only [p305action0Raw] using
      k305_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p305pair0Raw, threeRowAction_singleton] using
      k305_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k305_actual_channel0

 theorem k305_actual_channel1 :
    canonicalRowChannel k305occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((5-1).factorial : ℤ) •
        ((p305action1Raw)ᵀ * p305action1Raw - (p305pair1Raw)ᵀ * p305pair1Raw))) := by
  apply canonicalRowChannel_eq k305occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (5-1) (by omega)
    p305action1Raw p305pair1Raw
  · intro i a
    simpa only [p305action1Raw] using
      k305_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p305pair1Raw, threeRowAction_singleton] using
      k305_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k305_actual_channel1

 theorem k305_actual_channel2 :
    canonicalRowChannel k305occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 =
      complexify (integerForm (((5-2).factorial : ℤ) •
        ((p305action2Raw)ᵀ * p305action2Raw - (p305pair2Raw)ᵀ * p305pair2Raw))) := by
  apply canonicalRowChannel_eq k305occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 (5-2) (by omega)
    p305action2Raw p305pair2Raw
  · intro i a
    simpa only [p305action2Raw] using
      k305_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        ((frozenRows 2)[i.val]?.getD []) a
  · intro i a
    simpa only [p305pair2Raw, threeRowAction_singleton] using
      k305_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 2)[i.val]?.getD []) 0] a

#print axioms k305_actual_channel2

 theorem k305_actual_channel3 :
    canonicalRowChannel k305occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 =
      complexify (integerForm (((5-3).factorial : ℤ) •
        ((p305action3Raw)ᵀ * p305action3Raw - (p305pair3Raw)ᵀ * p305pair3Raw))) := by
  apply canonicalRowChannel_eq k305occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 (5-3) (by omega)
    p305action3Raw p305pair3Raw
  · intro i a
    simpa only [p305action3Raw] using
      k305_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        ((frozenRows 3)[i.val]?.getD []) a
  · intro i a
    simpa only [p305pair3Raw, threeRowAction_singleton] using
      k305_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 3)[i.val]?.getD []) 0] a

#print axioms k305_actual_channel3

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k305actualM3 : Matrix (Fin 5) (Fin 5) ℂ :=
  canonicalRowChannel k305occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k305occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 +
  canonicalRowChannel k305occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 +
  canonicalRowChannel k305occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3

theorem k305_actual_M3_raw : k305actualM3 = complexify p305rawMform := by
  unfold k305actualM3 p305rawMform p305rawNumerator
  rw [k305_actual_channel0, k305_actual_channel1, k305_actual_channel2, k305_actual_channel3]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k305_actual_M3_reconstructed : k305actualM3 = complexify p305Mform := by
  rw [k305_actual_M3_raw, p305_Mform_reconstructed]

#print axioms k305_actual_M3_raw
#print axioms k305_actual_M3_reconstructed

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k305_all_original_row_channels :
    canonicalAllRowChannels k305occ = k305actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k305occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k305occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k305occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k305occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k305actualM3
  simp only [add_zero, k305actualM3]

#print axioms k305_all_original_row_channels
end TorusLean.BosonFiniteCertificate
