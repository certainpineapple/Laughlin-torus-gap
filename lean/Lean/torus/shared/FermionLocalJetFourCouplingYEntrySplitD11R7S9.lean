import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 11 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-7650401962245334425 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 11 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-50249777324976288765 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 11 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-56078603229138562578645 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 11 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-8273426843720631083715 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 11 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((22401737359036739161515 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 11 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((436926499436756234266875 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 11 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-5885136330647645295 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R7S9 :
    OAI.Laughlin.Certificate.errorRational 11 (3 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (3 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R7S9Row0,
    originalYRowSplitD11R7S9Row1,
    originalYRowSplitD11R7S9Row2,
    originalYRowSplitD11R7S9Row3,
    originalYRowSplitD11R7S9Row4,
    originalYRowSplitD11R7S9Row5,
    originalYRowSplitD11R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
