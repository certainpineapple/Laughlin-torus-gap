import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R9S13Row0 :
    OAI.Laughlin.Certificate.yRow 14 9 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-385004202568044859800 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S13Row1 :
    OAI.Laughlin.Certificate.yRow 14 9 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-70486588923722346375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S13Row2 :
    OAI.Laughlin.Certificate.yRow 14 9 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1065211344470817385016175 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S13Row3 :
    OAI.Laughlin.Certificate.yRow 14 9 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-51506895476020277167875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S13Row4 :
    OAI.Laughlin.Certificate.yRow 14 9 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-425975337967943788049025 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S13Row5 :
    OAI.Laughlin.Certificate.yRow 14 9 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-28196660193738753684825 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S13Row6 :
    OAI.Laughlin.Certificate.yRow 14 9 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-11561506951340117546775 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R9S13 :
    OAI.Laughlin.Certificate.errorRational 14 (4 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (4 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 9 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R9S13Row0,
    originalYRowSplitD14R9S13Row1,
    originalYRowSplitD14R9S13Row2,
    originalYRowSplitD14R9S13Row3,
    originalYRowSplitD14R9S13Row4,
    originalYRowSplitD14R9S13Row5,
    originalYRowSplitD14R9S13Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R9S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
