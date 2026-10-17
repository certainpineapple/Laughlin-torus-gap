import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 13 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = (-123835152430838962575 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 13 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-145314884295340290135 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 13 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-320569257777802347592575 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 13 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-107791393369347960824475 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 13 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-9856115698548816286425 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 13 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-77938816150845300021525 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 13 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((4560872644031317284825 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R9S11 :
    OAI.Laughlin.Certificate.errorRational 13 (4 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (4 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R9S11Row0,
    originalYRowSplitD13R9S11Row1,
    originalYRowSplitD13R9S11Row2,
    originalYRowSplitD13R9S11Row3,
    originalYRowSplitD13R9S11Row4,
    originalYRowSplitD13R9S11Row5,
    originalYRowSplitD13R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
