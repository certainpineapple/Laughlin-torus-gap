import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 21 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 21 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 21 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 21 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 21 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((13752508205908718758066138959375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 21 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = (1345771964461408755906009375 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 21 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1853544372915223315817368003125 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R1S1 :
    OAI.Laughlin.Certificate.errorRational 21 (0 : Fin 11) (0 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (0 : Fin 11) (0 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R1S1Row0,
    originalYRowSplitD21R1S1Row1,
    originalYRowSplitD21R1S1Row2,
    originalYRowSplitD21R1S1Row3,
    originalYRowSplitD21R1S1Row4,
    originalYRowSplitD21R1S1Row5,
    originalYRowSplitD21R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
