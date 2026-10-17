import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 11 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-255003080564178753975 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 11 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-840285334819910278125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 11 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5821409776653409023937125 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 11 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-319202647665629720313825 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 11 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((159577610183405495181225 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 11 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-6874248778647063814164375 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 11 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((12579830806102722147825 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R1S9 :
    OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (0 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R1S9Row0,
    originalYRowSplitD11R1S9Row1,
    originalYRowSplitD11R1S9Row2,
    originalYRowSplitD11R1S9Row3,
    originalYRowSplitD11R1S9Row4,
    originalYRowSplitD11R1S9Row5,
    originalYRowSplitD11R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
