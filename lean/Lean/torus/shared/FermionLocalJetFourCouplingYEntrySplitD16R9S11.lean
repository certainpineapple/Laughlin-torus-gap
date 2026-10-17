import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 16 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = (479131037553139240500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 16 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-21402449520440459625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 16 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-450827060725384237125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 16 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((641788849340561814073875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 16 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-225363383117829899798625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 16 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((279585255852535475390625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 16 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-37506987409247690536125 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R9S11 :
    OAI.Laughlin.Certificate.errorRational 16 (4 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (4 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R9S11Row0,
    originalYRowSplitD16R9S11Row1,
    originalYRowSplitD16R9S11Row2,
    originalYRowSplitD16R9S11Row3,
    originalYRowSplitD16R9S11Row4,
    originalYRowSplitD16R9S11Row5,
    originalYRowSplitD16R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
