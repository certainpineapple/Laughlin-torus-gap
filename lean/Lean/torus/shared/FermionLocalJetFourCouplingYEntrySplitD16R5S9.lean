import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 16 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = (1584039888950402787750 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 16 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-370163945708432308125 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 16 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-21207103437667845592125 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 16 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-3496174753173526062205875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 16 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((4105945961571820720575375 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 16 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-139800617122070703211875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 16 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((397701677388950597383875 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R5S9 :
    OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (2 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R5S9Row0,
    originalYRowSplitD16R5S9Row1,
    originalYRowSplitD16R5S9Row2,
    originalYRowSplitD16R5S9Row3,
    originalYRowSplitD16R5S9Row4,
    originalYRowSplitD16R5S9Row5,
    originalYRowSplitD16R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
