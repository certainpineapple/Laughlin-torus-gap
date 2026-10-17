import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R3S13Row0 :
    OAI.Laughlin.Certificate.yRow 17 3 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S13Row1 :
    OAI.Laughlin.Certificate.yRow 17 3 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-18311442175435440806775 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S13Row2 :
    OAI.Laughlin.Certificate.yRow 17 3 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((4655385038702095939966725 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S13Row3 :
    OAI.Laughlin.Certificate.yRow 17 3 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((1588289292696434247144225 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S13Row4 :
    OAI.Laughlin.Certificate.yRow 17 3 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-192299784107660673454135125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S13Row5 :
    OAI.Laughlin.Certificate.yRow 17 3 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((11184558407242475894013375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S13Row6 :
    OAI.Laughlin.Certificate.yRow 17 3 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-4008318180903822863852775 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R3S13 :
    OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (1 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 3 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R3S13Row0,
    originalYRowSplitD17R3S13Row1,
    originalYRowSplitD17R3S13Row2,
    originalYRowSplitD17R3S13Row3,
    originalYRowSplitD17R3S13Row4,
    originalYRowSplitD17R3S13Row5,
    originalYRowSplitD17R3S13Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R3S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
