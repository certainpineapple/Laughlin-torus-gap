import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((137740445604110246522625 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((315664301427107975166825 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((581503278298949395041477825 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((63977548486724629839257175 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((32344775635045968898078275 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-479359848706329356360820225 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((5242059377826352839432675 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S11 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S11Row0,
    originalYRowSplitD15R1S11Row1,
    originalYRowSplitD15R1S11Row2,
    originalYRowSplitD15R1S11Row3,
    originalYRowSplitD15R1S11Row4,
    originalYRowSplitD15R1S11Row5,
    originalYRowSplitD15R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
