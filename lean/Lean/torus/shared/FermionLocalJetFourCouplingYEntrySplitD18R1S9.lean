import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((5816092307857550858514375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((1666802490815874475511823375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-16419702229029234777802285125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((120257418243066952539817125 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S9 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S9Row0,
    originalYRowSplitD18R1S9Row1,
    originalYRowSplitD18R1S9Row2,
    originalYRowSplitD18R1S9Row3,
    originalYRowSplitD18R1S9Row4,
    originalYRowSplitD18R1S9Row5,
    originalYRowSplitD18R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
