import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 15 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = (-21934241008372192500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 15 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((448516258341005356425 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 15 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-239471773207885466099775 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 15 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-206666569836111290407425 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 15 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((19679328324376236912825 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 15 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((872751492847425955205475 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 15 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((1884870099110765341575 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R9S11 :
    OAI.Laughlin.Certificate.errorRational 15 (4 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (4 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R9S11Row0,
    originalYRowSplitD15R9S11Row1,
    originalYRowSplitD15R9S11Row2,
    originalYRowSplitD15R9S11Row3,
    originalYRowSplitD15R9S11Row4,
    originalYRowSplitD15R9S11Row5,
    originalYRowSplitD15R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
