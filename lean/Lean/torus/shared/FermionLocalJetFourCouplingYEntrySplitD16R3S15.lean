import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R3S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 3 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-48448033002345992140125 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 3 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-938794973484665422125 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 3 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((44160286719546727787932875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 3 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-53350126451556275659192875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 3 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-164349558222559854916897125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 3 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-222029909600700075300050625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 3 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((1839385561132325970138375 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R3S15 :
    OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (1 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 3 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R3S15Row0,
    originalYRowSplitD16R3S15Row1,
    originalYRowSplitD16R3S15Row2,
    originalYRowSplitD16R3S15Row3,
    originalYRowSplitD16R3S15Row4,
    originalYRowSplitD16R3S15Row5,
    originalYRowSplitD16R3S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R3S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
