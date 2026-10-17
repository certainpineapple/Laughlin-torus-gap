import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 11 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-1265493359900399175 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 11 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-50108210149231990125 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 11 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((246772026834405186112875 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 11 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-21552737764927882226175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 11 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-59511726712055121929325 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 11 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((1043175292936938107566875 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 11 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((557432897585470377975 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R5S7 :
    OAI.Laughlin.Certificate.errorRational 11 (2 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (2 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R5S7Row0,
    originalYRowSplitD11R5S7Row1,
    originalYRowSplitD11R5S7Row2,
    originalYRowSplitD11R5S7Row3,
    originalYRowSplitD11R5S7Row4,
    originalYRowSplitD11R5S7Row5,
    originalYRowSplitD11R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
