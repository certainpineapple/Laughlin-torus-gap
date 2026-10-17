import torus.shared.BosonFiniteCertificateCanonicalRows306
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

 theorem k306_actual_channel0 :
    canonicalRowChannel k306occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((6-0).factorial : ℤ) •
        ((p306action0Raw)ᵀ * p306action0Raw - (p306pair0Raw)ᵀ * p306pair0Raw))) := by
  apply canonicalRowChannel_eq k306occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (6-0) (by omega)
    p306action0Raw p306pair0Raw
  · intro i a
    simpa only [p306action0Raw] using
      k306_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p306pair0Raw, threeRowAction_singleton] using
      k306_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k306_actual_channel0

 theorem k306_actual_channel1 :
    canonicalRowChannel k306occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((6-1).factorial : ℤ) •
        ((p306action1Raw)ᵀ * p306action1Raw - (p306pair1Raw)ᵀ * p306pair1Raw))) := by
  apply canonicalRowChannel_eq k306occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (6-1) (by omega)
    p306action1Raw p306pair1Raw
  · intro i a
    simpa only [p306action1Raw] using
      k306_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p306pair1Raw, threeRowAction_singleton] using
      k306_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k306_actual_channel1

 theorem k306_actual_channel2 :
    canonicalRowChannel k306occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 =
      complexify (integerForm (((6-2).factorial : ℤ) •
        ((p306action2Raw)ᵀ * p306action2Raw - (p306pair2Raw)ᵀ * p306pair2Raw))) := by
  apply canonicalRowChannel_eq k306occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 (6-2) (by omega)
    p306action2Raw p306pair2Raw
  · intro i a
    simpa only [p306action2Raw] using
      k306_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        ((frozenRows 2)[i.val]?.getD []) a
  · intro i a
    simpa only [p306pair2Raw, threeRowAction_singleton] using
      k306_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 2)[i.val]?.getD []) 0] a

#print axioms k306_actual_channel2

 theorem k306_actual_channel3 :
    canonicalRowChannel k306occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 =
      complexify (integerForm (((6-3).factorial : ℤ) •
        ((p306action3Raw)ᵀ * p306action3Raw - (p306pair3Raw)ᵀ * p306pair3Raw))) := by
  apply canonicalRowChannel_eq k306occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 (6-3) (by omega)
    p306action3Raw p306pair3Raw
  · intro i a
    simpa only [p306action3Raw] using
      k306_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        ((frozenRows 3)[i.val]?.getD []) a
  · intro i a
    simpa only [p306pair3Raw, threeRowAction_singleton] using
      k306_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 3)[i.val]?.getD []) 0] a

#print axioms k306_actual_channel3

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k306actualM3 : Matrix (Fin 7) (Fin 7) ℂ :=
  canonicalRowChannel k306occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k306occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 +
  canonicalRowChannel k306occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 +
  canonicalRowChannel k306occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3

theorem k306_actual_M3_raw : k306actualM3 = complexify p306rawMform := by
  unfold k306actualM3 p306rawMform p306rawNumerator
  rw [k306_actual_channel0, k306_actual_channel1, k306_actual_channel2, k306_actual_channel3]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k306_actual_M3_reconstructed : k306actualM3 = complexify p306Mform := by
  rw [k306_actual_M3_raw, p306_Mform_reconstructed]

#print axioms k306_actual_M3_raw
#print axioms k306_actual_M3_reconstructed

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k306_all_original_row_channels :
    canonicalAllRowChannels k306occ = k306actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k306occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k306occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k306occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k306occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k306actualM3
  simp only [add_zero, k306actualM3]

#print axioms k306_all_original_row_channels
end TorusLean.BosonFiniteCertificate
