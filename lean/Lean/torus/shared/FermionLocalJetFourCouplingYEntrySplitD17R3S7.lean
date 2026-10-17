import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 17 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 17 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((25404638607195964491375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 17 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((14649170892748015853604375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 17 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1828737471976452882219375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 17 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((116456801003351466497965125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 17 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-286437114155512883083145625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 17 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-4631530261259862269434125 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R3S7 :
    OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (1 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R3S7Row0,
    originalYRowSplitD17R3S7Row1,
    originalYRowSplitD17R3S7Row2,
    originalYRowSplitD17R3S7Row3,
    originalYRowSplitD17R3S7Row4,
    originalYRowSplitD17R3S7Row5,
    originalYRowSplitD17R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
