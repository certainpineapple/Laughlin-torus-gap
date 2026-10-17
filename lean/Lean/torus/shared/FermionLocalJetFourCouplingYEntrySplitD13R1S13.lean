import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 13 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = ((7824351705901302847275 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 13 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((23972406218739176880825 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 13 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((770672695703679421892521425 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 13 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((9544831078684914477840375 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 13 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-36647886158090279097436125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 13 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((22636769335555562295419025 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 13 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((1184121786690060091698825 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R1S13 :
    OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (0 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R1S13Row0,
    originalYRowSplitD13R1S13Row1,
    originalYRowSplitD13R1S13Row2,
    originalYRowSplitD13R1S13Row3,
    originalYRowSplitD13R1S13Row4,
    originalYRowSplitD13R1S13Row5,
    originalYRowSplitD13R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
