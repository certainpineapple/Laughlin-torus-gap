import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 17 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 17 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-2381779491736534745625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 17 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-34731102377875428149625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 17 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((11791261180853566594875 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 17 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-40460894326048516767995625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 17 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((84760649364625712579091375 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 17 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-4196350813177677695223375 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R5S9 :
    OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (2 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R5S9Row0,
    originalYRowSplitD17R5S9Row1,
    originalYRowSplitD17R5S9Row2,
    originalYRowSplitD17R5S9Row3,
    originalYRowSplitD17R5S9Row4,
    originalYRowSplitD17R5S9Row5,
    originalYRowSplitD17R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
