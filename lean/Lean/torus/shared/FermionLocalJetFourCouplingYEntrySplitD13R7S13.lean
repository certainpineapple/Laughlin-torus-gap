import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R7S13Row0 :
    OAI.Laughlin.Certificate.yRow 13 7 13
      (OAI.Laughlin.Certificate.rows[0]!) = (439602157711314172575 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S13Row1 :
    OAI.Laughlin.Certificate.yRow 13 7 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((2202150437981720193825 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S13Row2 :
    OAI.Laughlin.Certificate.yRow 13 7 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((80959932519207324350625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S13Row3 :
    OAI.Laughlin.Certificate.yRow 13 7 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((71387092767179374710525 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S13Row4 :
    OAI.Laughlin.Certificate.yRow 13 7 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-452907217531635191871975 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S13Row5 :
    OAI.Laughlin.Certificate.yRow 13 7 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((758797173040697943899175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S13Row6 :
    OAI.Laughlin.Certificate.yRow 13 7 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-6807680366865601798575 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R7S13 :
    OAI.Laughlin.Certificate.errorRational 13 (3 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (3 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 7 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R7S13Row0,
    originalYRowSplitD13R7S13Row1,
    originalYRowSplitD13R7S13Row2,
    originalYRowSplitD13R7S13Row3,
    originalYRowSplitD13R7S13Row4,
    originalYRowSplitD13R7S13Row5,
    originalYRowSplitD13R7S13Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R7S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
