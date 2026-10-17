import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R7S13Row0 :
    OAI.Laughlin.Certificate.yRow 16 7 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-12344893554823830000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S13Row1 :
    OAI.Laughlin.Certificate.yRow 16 7 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-318210811783069330125 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S13Row2 :
    OAI.Laughlin.Certificate.yRow 16 7 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((235436143873617859597425 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S13Row3 :
    OAI.Laughlin.Certificate.yRow 16 7 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((4567072492372996561430475 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S13Row4 :
    OAI.Laughlin.Certificate.yRow 16 7 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-122887445842049388625125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S13Row5 :
    OAI.Laughlin.Certificate.yRow 16 7 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((35552328163344079483421025 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S13Row6 :
    OAI.Laughlin.Certificate.yRow 16 7 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-9870679093708897088625 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R7S13 :
    OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (3 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 7 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R7S13Row0,
    originalYRowSplitD16R7S13Row1,
    originalYRowSplitD16R7S13Row2,
    originalYRowSplitD16R7S13Row3,
    originalYRowSplitD16R7S13Row4,
    originalYRowSplitD16R7S13Row5,
    originalYRowSplitD16R7S13Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R7S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
