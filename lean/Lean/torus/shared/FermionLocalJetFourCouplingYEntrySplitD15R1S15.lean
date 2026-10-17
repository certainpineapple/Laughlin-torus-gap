import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 15
      (OAI.Laughlin.Certificate.rows[0]!) = (1722787967907664988455125 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-8331281513786978548176375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((18044398521289412630423690625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((46150363886322143500927875 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-452285111369925607534385625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2901896681061061741601919375 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((6311171054350334678380875 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S15 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S15Row0,
    originalYRowSplitD15R1S15Row1,
    originalYRowSplitD15R1S15Row2,
    originalYRowSplitD15R1S15Row3,
    originalYRowSplitD15R1S15Row4,
    originalYRowSplitD15R1S15Row5,
    originalYRowSplitD15R1S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
