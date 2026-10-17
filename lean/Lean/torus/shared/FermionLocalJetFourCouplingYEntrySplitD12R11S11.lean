import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 12 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((158144778046736729325 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 12 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((72991586777637461175 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 12 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((726758721082614447060075 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 12 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((989284187069024024853675 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 12 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-36975506208979494679875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 12 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((193898136433833276085575 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 12 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-8314202420181874391175 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R11S11 :
    OAI.Laughlin.Certificate.errorRational 12 (5 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (5 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R11S11Row0,
    originalYRowSplitD12R11S11Row1,
    originalYRowSplitD12R11S11Row2,
    originalYRowSplitD12R11S11Row3,
    originalYRowSplitD12R11S11Row4,
    originalYRowSplitD12R11S11Row5,
    originalYRowSplitD12R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
