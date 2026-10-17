import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 13 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((501074108039899650375 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 13 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((2520287874332051806125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 13 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((2165486084723415969727425 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 13 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-69676437876919471223325 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 13 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((774201581414259212602575 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 13 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-50782889417218958010375 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 13 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-3721170465091299989475 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R3S7 :
    OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (1 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R3S7Row0,
    originalYRowSplitD13R3S7Row1,
    originalYRowSplitD13R3S7Row2,
    originalYRowSplitD13R3S7Row3,
    originalYRowSplitD13R3S7Row4,
    originalYRowSplitD13R3S7Row5,
    originalYRowSplitD13R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
