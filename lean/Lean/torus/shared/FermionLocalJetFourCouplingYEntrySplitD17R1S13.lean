import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 17 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 17 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-51875504096078693905875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 17 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((22504658926723562361898125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 17 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = (-156924636883272259501500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 17 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((412502630805746822301085125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 17 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((1932166710232569719581798125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 17 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((63823010932555018414144875 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R1S13 :
    OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (0 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R1S13Row0,
    originalYRowSplitD17R1S13Row1,
    originalYRowSplitD17R1S13Row2,
    originalYRowSplitD17R1S13Row3,
    originalYRowSplitD17R1S13Row4,
    originalYRowSplitD17R1S13Row5,
    originalYRowSplitD17R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
