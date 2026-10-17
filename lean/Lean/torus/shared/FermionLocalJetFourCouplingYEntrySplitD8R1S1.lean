import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 8 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((-1542335899954614345 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 8 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((-75316015709295173739 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 8 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((-9136760184633772519965 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 8 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((526208461257856971342675 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 8 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((14597567158110194070375 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 8 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-347441421785295611479515 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 8 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-8205115144686782088375 / 16777216) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R1S1 :
    OAI.Laughlin.Certificate.errorRational 8 (0 : Fin 4) (0 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (0 : Fin 4) (0 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R1S1Row0,
    originalYRowSplitD8R1S1Row1,
    originalYRowSplitD8R1S1Row2,
    originalYRowSplitD8R1S1Row3,
    originalYRowSplitD8R1S1Row4,
    originalYRowSplitD8R1S1Row5,
    originalYRowSplitD8R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
