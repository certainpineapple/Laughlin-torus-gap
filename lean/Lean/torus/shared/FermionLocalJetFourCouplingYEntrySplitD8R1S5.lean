import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 8 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-14645438327407983795 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 8 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-18171099948981591081 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 8 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-35901747833688299761245 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 8 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((13068275739016009424895 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 8 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-102541802088869818905 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 8 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-142185036639416818007445 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 8 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-177811778631486817125 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R1S5 :
    OAI.Laughlin.Certificate.errorRational 8 (0 : Fin 4) (2 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (0 : Fin 4) (2 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R1S5Row0,
    originalYRowSplitD8R1S5Row1,
    originalYRowSplitD8R1S5Row2,
    originalYRowSplitD8R1S5Row3,
    originalYRowSplitD8R1S5Row4,
    originalYRowSplitD8R1S5Row5,
    originalYRowSplitD8R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
