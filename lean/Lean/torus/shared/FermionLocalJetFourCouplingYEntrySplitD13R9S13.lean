import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R9S13Row0 :
    OAI.Laughlin.Certificate.yRow 13 9 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-72412584454683673200 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S13Row1 :
    OAI.Laughlin.Certificate.yRow 13 9 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((806789874003823317465 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S13Row2 :
    OAI.Laughlin.Certificate.yRow 13 9 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((1687040779104369197276625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S13Row3 :
    OAI.Laughlin.Certificate.yRow 13 9 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-67192095376043455442625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S13Row4 :
    OAI.Laughlin.Certificate.yRow 13 9 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((436008254545426252543425 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S13Row5 :
    OAI.Laughlin.Certificate.yRow 13 9 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-496425066743942092174275 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S13Row6 :
    OAI.Laughlin.Certificate.yRow 13 9 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-16579839198934036750725 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R9S13 :
    OAI.Laughlin.Certificate.errorRational 13 (4 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (4 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 9 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R9S13Row0,
    originalYRowSplitD13R9S13Row1,
    originalYRowSplitD13R9S13Row2,
    originalYRowSplitD13R9S13Row3,
    originalYRowSplitD13R9S13Row4,
    originalYRowSplitD13R9S13Row5,
    originalYRowSplitD13R9S13Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R9S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
