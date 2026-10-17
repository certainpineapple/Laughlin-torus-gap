import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((366731522749390189041275625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((107859117638507890999719375 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((-3914809321339003400648960625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((-66202224467370350486902149375 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((8277400159283467077491500875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-132860733135158786560781603625 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-15558332212343932302205789875 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S1 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (0 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (0 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S1Row0,
    originalYRowSplitD16R1S1Row1,
    originalYRowSplitD16R1S1Row2,
    originalYRowSplitD16R1S1Row3,
    originalYRowSplitD16R1S1Row4,
    originalYRowSplitD16R1S1Row5,
    originalYRowSplitD16R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
