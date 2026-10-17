import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 14 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = (-69524524106595288675 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 14 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((258631648843619594025 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 14 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-307074702388568867412975 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 14 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-354953175803007892332075 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 14 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-342532557425153962007775 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 14 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((4073057093762053146147825 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 14 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((20632657709950590252375 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R5S9 :
    OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (2 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R5S9Row0,
    originalYRowSplitD14R5S9Row1,
    originalYRowSplitD14R5S9Row2,
    originalYRowSplitD14R5S9Row3,
    originalYRowSplitD14R5S9Row4,
    originalYRowSplitD14R5S9Row5,
    originalYRowSplitD14R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
