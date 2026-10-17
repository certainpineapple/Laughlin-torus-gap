import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 17 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 17 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((71970215207566217416875 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 17 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((70815752458682271524859375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 17 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-737265324087263055459375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 17 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-533676847753548985133773125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 17 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((3753845519214312826735055625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 17 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((114241759173748735239335625 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R1S7 :
    OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (0 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R1S7Row0,
    originalYRowSplitD17R1S7Row1,
    originalYRowSplitD17R1S7Row2,
    originalYRowSplitD17R1S7Row3,
    originalYRowSplitD17R1S7Row4,
    originalYRowSplitD17R1S7Row5,
    originalYRowSplitD17R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
