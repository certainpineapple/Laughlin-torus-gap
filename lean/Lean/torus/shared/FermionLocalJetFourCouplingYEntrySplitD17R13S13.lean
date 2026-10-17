import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R13S13Row0 :
    OAI.Laughlin.Certificate.yRow 17 13 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S13Row1 :
    OAI.Laughlin.Certificate.yRow 17 13 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((115443178189265151225 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S13Row2 :
    OAI.Laughlin.Certificate.yRow 17 13 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((249593314582691447393025 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S13Row3 :
    OAI.Laughlin.Certificate.yRow 17 13 13
      (OAI.Laughlin.Certificate.rows[3]!) = (48345945859058934136050 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S13Row4 :
    OAI.Laughlin.Certificate.yRow 17 13 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1269077763752020559390625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S13Row5 :
    OAI.Laughlin.Certificate.yRow 17 13 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-15265166376790777865900625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S13Row6 :
    OAI.Laughlin.Certificate.yRow 17 13 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((132171975074324419108875 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R13S13 :
    OAI.Laughlin.Certificate.errorRational 17 (6 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (6 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 13 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R13S13Row0,
    originalYRowSplitD17R13S13Row1,
    originalYRowSplitD17R13S13Row2,
    originalYRowSplitD17R13S13Row3,
    originalYRowSplitD17R13S13Row4,
    originalYRowSplitD17R13S13Row5,
    originalYRowSplitD17R13S13Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R13S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
