import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((-14114967847064857184937525 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((-84449807087385196434752775 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((235216755549836987924204031825 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((1625409443591028274126372425 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((4257319530488198622123701025 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-37098173921171893732342965825 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-983692792969359710157545625 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S1 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (0 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (0 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S1Row0,
    originalYRowSplitD15R1S1Row1,
    originalYRowSplitD15R1S1Row2,
    originalYRowSplitD15R1S1Row3,
    originalYRowSplitD15R1S1Row4,
    originalYRowSplitD15R1S1Row5,
    originalYRowSplitD15R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
