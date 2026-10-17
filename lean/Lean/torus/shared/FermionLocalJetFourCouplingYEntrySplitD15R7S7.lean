import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 15 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((914658929622618980625 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 15 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((5624291778722603013825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 15 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((7320117149457827870646225 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 15 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((562858447785485324985225 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 15 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((8212378365246182972498325 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 15 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-6661731904978042723869675 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 15 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-189979299260490863322675 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R7S7 :
    OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (3 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R7S7Row0,
    originalYRowSplitD15R7S7Row1,
    originalYRowSplitD15R7S7Row2,
    originalYRowSplitD15R7S7Row3,
    originalYRowSplitD15R7S7Row4,
    originalYRowSplitD15R7S7Row5,
    originalYRowSplitD15R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
