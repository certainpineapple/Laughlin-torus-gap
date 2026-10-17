import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 15 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-10782564436746609940125 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 15 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-39198360581761491824175 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 15 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-19900447073306418321046575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 15 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((2466491000412136641329925 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 15 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((3455623561146108727965975 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 15 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-34884532331214799923337725 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 15 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((144230054344281062682525 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R3S7 :
    OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (1 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R3S7Row0,
    originalYRowSplitD15R3S7Row1,
    originalYRowSplitD15R3S7Row2,
    originalYRowSplitD15R3S7Row3,
    originalYRowSplitD15R3S7Row4,
    originalYRowSplitD15R3S7Row5,
    originalYRowSplitD15R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
