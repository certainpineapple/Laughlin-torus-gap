import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 10 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-20624330933689828275 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 10 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((13580205637829379975 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 10 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-34010565328912928443425 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 10 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-196967258788969923975 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 10 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((16740483622089229741725 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 10 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((1565059269986402303925 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 10 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-428458437116959471425 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R5S9 :
    OAI.Laughlin.Certificate.errorRational 10 (2 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (2 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R5S9Row0,
    originalYRowSplitD10R5S9Row1,
    originalYRowSplitD10R5S9Row2,
    originalYRowSplitD10R5S9Row3,
    originalYRowSplitD10R5S9Row4,
    originalYRowSplitD10R5S9Row5,
    originalYRowSplitD10R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
