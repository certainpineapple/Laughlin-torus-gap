import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R13S13Row0 :
    OAI.Laughlin.Certificate.yRow 18 13 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S13Row1 :
    OAI.Laughlin.Certificate.yRow 18 13 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S13Row2 :
    OAI.Laughlin.Certificate.yRow 18 13 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S13Row3 :
    OAI.Laughlin.Certificate.yRow 18 13 13
      (OAI.Laughlin.Certificate.rows[3]!) = (37262211994821418605000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S13Row4 :
    OAI.Laughlin.Certificate.yRow 18 13 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2612231755088903038216125 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S13Row5 :
    OAI.Laughlin.Certificate.yRow 18 13 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-6406626451878181566662625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S13Row6 :
    OAI.Laughlin.Certificate.yRow 18 13 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-81049440867704396962875 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R13S13 :
    OAI.Laughlin.Certificate.errorRational 18 (6 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (6 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 13 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R13S13Row0,
    originalYRowSplitD18R13S13Row1,
    originalYRowSplitD18R13S13Row2,
    originalYRowSplitD18R13S13Row3,
    originalYRowSplitD18R13S13Row4,
    originalYRowSplitD18R13S13Row5,
    originalYRowSplitD18R13S13Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R13S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
