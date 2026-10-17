import torus.shared.BosonFiniteCertificateCanonicalRows308
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

 theorem k308_actual_channel0 :
    canonicalRowChannel k308occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 =
      complexify (integerForm (((8-0).factorial : ℤ) •
        ((p308action0Raw)ᵀ * p308action0Raw - (p308pair0Raw)ᵀ * p308pair0Raw))) := by
  apply canonicalRowChannel_eq k308occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 (8-0) (by omega)
    p308action0Raw p308pair0Raw
  · intro i a
    simpa only [p308action0Raw] using
      k308_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        ((frozenRows 0)[i.val]?.getD []) a
  · intro i a
    simpa only [p308pair0Raw, threeRowAction_singleton] using
      k308_actual_canonical_row (⟨0, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 0)[i.val]?.getD []) 0] a

#print axioms k308_actual_channel0

 theorem k308_actual_channel1 :
    canonicalRowChannel k308occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 =
      complexify (integerForm (((8-1).factorial : ℤ) •
        ((p308action1Raw)ᵀ * p308action1Raw - (p308pair1Raw)ᵀ * p308pair1Raw))) := by
  apply canonicalRowChannel_eq k308occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 (8-1) (by omega)
    p308action1Raw p308pair1Raw
  · intro i a
    simpa only [p308action1Raw] using
      k308_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        ((frozenRows 1)[i.val]?.getD []) a
  · intro i a
    simpa only [p308pair1Raw, threeRowAction_singleton] using
      k308_actual_canonical_row (⟨1, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 1)[i.val]?.getD []) 0] a

#print axioms k308_actual_channel1

 theorem k308_actual_channel2 :
    canonicalRowChannel k308occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 =
      complexify (integerForm (((8-2).factorial : ℤ) •
        ((p308action2Raw)ᵀ * p308action2Raw - (p308pair2Raw)ᵀ * p308pair2Raw))) := by
  apply canonicalRowChannel_eq k308occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 (8-2) (by omega)
    p308action2Raw p308pair2Raw
  · intro i a
    simpa only [p308action2Raw] using
      k308_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        ((frozenRows 2)[i.val]?.getD []) a
  · intro i a
    simpa only [p308pair2Raw, threeRowAction_singleton] using
      k308_actual_canonical_row (⟨2, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 2)[i.val]?.getD []) 0] a

#print axioms k308_actual_channel2

 theorem k308_actual_channel3 :
    canonicalRowChannel k308occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 =
      complexify (integerForm (((8-3).factorial : ℤ) •
        ((p308action3Raw)ᵀ * p308action3Raw - (p308pair3Raw)ᵀ * p308pair3Raw))) := by
  apply canonicalRowChannel_eq k308occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3 (8-3) (by omega)
    p308action3Raw p308pair3Raw
  · intro i a
    simpa only [p308action3Raw] using
      k308_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        ((frozenRows 3)[i.val]?.getD []) a
  · intro i a
    simpa only [p308pair3Raw, threeRowAction_singleton] using
      k308_actual_canonical_row (⟨3, by decide⟩ : Fin 4)
        [rowInteger ((frozenRows 3)[i.val]?.getD []) 0] a

#print axioms k308_actual_channel3

/-- Full original finite-row anchored three-particle form, as true canonical
row-square inner products minus their pure two-body row-square parts. -/
def k308actualM3 : Matrix (Fin 10) (Fin 10) ℂ :=
  canonicalRowChannel k308occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0 +
  canonicalRowChannel k308occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1 +
  canonicalRowChannel k308occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2 +
  canonicalRowChannel k308occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3

theorem k308_actual_M3_raw : k308actualM3 = complexify p308rawMform := by
  unfold k308actualM3 p308rawMform p308rawNumerator
  rw [k308_actual_channel0, k308_actual_channel1, k308_actual_channel2, k308_actual_channel3]
  norm_num only [Nat.reduceSub, Nat.factorial, ← complexify_add_rect, ← integerForm_add]

theorem k308_actual_M3_reconstructed : k308actualM3 = complexify p308Mform := by
  rw [k308_actual_M3_raw, p308_Mform_reconstructed]

#print axioms k308_actual_M3_raw
#print axioms k308_actual_M3_reconstructed

/-- All four published channels, including all 138 original rows, agree with
this block's source form. Above-degree channels vanish by degree conservation. -/
theorem k308_all_original_row_channels :
    canonicalAllRowChannels k308occ = k308actualM3 := by
  simp only [canonicalAllRowChannels, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [add_zero, ← add_assoc]
  change (canonicalRowChannel k308occ (fun i : Fin 31 => ((frozenRows 0)[i.val]?.getD [])) 0) + (canonicalRowChannel k308occ (fun i : Fin 37 => ((frozenRows 1)[i.val]?.getD [])) 1) + (canonicalRowChannel k308occ (fun i : Fin 36 => ((frozenRows 2)[i.val]?.getD [])) 2) + (canonicalRowChannel k308occ (fun i : Fin 34 => ((frozenRows 3)[i.val]?.getD [])) 3) = k308actualM3
  simp only [add_zero, k308actualM3]

#print axioms k308_all_original_row_channels
end TorusLean.BosonFiniteCertificate
