import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 10 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((64780381883064099105 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 10 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((31790314147172660235 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 10 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((155346215928025527757935 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 10 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((48520055300304697866855 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 10 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((107038246187026842362055 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 10 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-74027173474771396535115 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 10 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-243325559643498511515 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R3S9 :
    OAI.Laughlin.Certificate.errorRational 10 (1 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (1 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R3S9Row0,
    originalYRowSplitD10R3S9Row1,
    originalYRowSplitD10R3S9Row2,
    originalYRowSplitD10R3S9Row3,
    originalYRowSplitD10R3S9Row4,
    originalYRowSplitD10R3S9Row5,
    originalYRowSplitD10R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
