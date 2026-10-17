import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R13S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 13 15
      (OAI.Laughlin.Certificate.rows[0]!) = (33571083735744963408000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 13 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-11382776180424656382375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 13 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-77106382551663978447309375 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 13 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((4404401068058554971783375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 13 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((25225419351876564790344375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 13 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-41388594960788372558386125 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 13 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R13S15 :
    OAI.Laughlin.Certificate.errorRational 15 (6 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (6 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 13 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R13S15Row0,
    originalYRowSplitD15R13S15Row1,
    originalYRowSplitD15R13S15Row2,
    originalYRowSplitD15R13S15Row3,
    originalYRowSplitD15R13S15Row4,
    originalYRowSplitD15R13S15Row5,
    originalYRowSplitD15R13S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R13S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
