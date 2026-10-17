import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R13S13Row0 :
    OAI.Laughlin.Certificate.yRow 13 13 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-2500164423476654734800 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R13S13Row1 :
    OAI.Laughlin.Certificate.yRow 13 13 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((18427471552482493869225 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R13S13Row2 :
    OAI.Laughlin.Certificate.yRow 13 13 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((122222416971238906560606225 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R13S13Row3 :
    OAI.Laughlin.Certificate.yRow 13 13 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((4215943629673377963235875 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R13S13Row4 :
    OAI.Laughlin.Certificate.yRow 13 13 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((2789570767575937147706475 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R13S13Row5 :
    OAI.Laughlin.Certificate.yRow 13 13 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((833570102589840456115275 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R13S13Row6 :
    OAI.Laughlin.Certificate.yRow 13 13 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((17567769625443212175 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R13S13 :
    OAI.Laughlin.Certificate.errorRational 13 (6 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (6 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 13 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R13S13Row0,
    originalYRowSplitD13R13S13Row1,
    originalYRowSplitD13R13S13Row2,
    originalYRowSplitD13R13S13Row3,
    originalYRowSplitD13R13S13Row4,
    originalYRowSplitD13R13S13Row5,
    originalYRowSplitD13R13S13Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R13S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
