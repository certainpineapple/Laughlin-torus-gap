import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-709476700697045045139375 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-235596173769966123489375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((131952647237678457261946875 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-259933071178721103809270625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((370488570968829776299711875 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((3601154573546068878239525625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-9196927805661629850691875 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S15 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S15Row0,
    originalYRowSplitD16R1S15Row1,
    originalYRowSplitD16R1S15Row2,
    originalYRowSplitD16R1S15Row3,
    originalYRowSplitD16R1S15Row4,
    originalYRowSplitD16R1S15Row5,
    originalYRowSplitD16R1S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
