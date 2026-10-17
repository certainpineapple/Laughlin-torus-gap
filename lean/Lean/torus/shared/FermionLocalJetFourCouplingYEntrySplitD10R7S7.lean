import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 10 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-8752482634216159125 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 10 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-13434422302104022305 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 10 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((18875445278186819534175 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 10 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((5017480876065396637395 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 10 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-7156607940123661968615 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 10 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((26610967094853422668005 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 10 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-942658139913752028375 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R7S7 :
    OAI.Laughlin.Certificate.errorRational 10 (3 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (3 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R7S7Row0,
    originalYRowSplitD10R7S7Row1,
    originalYRowSplitD10R7S7Row2,
    originalYRowSplitD10R7S7Row3,
    originalYRowSplitD10R7S7Row4,
    originalYRowSplitD10R7S7Row5,
    originalYRowSplitD10R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
