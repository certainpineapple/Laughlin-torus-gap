import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 13 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-39632345938126331775 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 13 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-247312793971542659175 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 13 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-243136984554073696006575 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 13 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-160094256228873404800425 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 13 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((305653032455313451429575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 13 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-569603312029772094093525 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 13 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1076364144289095557175 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R5S9 :
    OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (2 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R5S9Row0,
    originalYRowSplitD13R5S9Row1,
    originalYRowSplitD13R5S9Row2,
    originalYRowSplitD13R5S9Row3,
    originalYRowSplitD13R5S9Row4,
    originalYRowSplitD13R5S9Row5,
    originalYRowSplitD13R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
