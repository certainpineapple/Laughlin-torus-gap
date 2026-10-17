import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 17 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 17 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((64757290299457540640625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 17 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((9814462128438883688705625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 17 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((180296618579054127005625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 17 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((796477067173872351110559375 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 17 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-3656580978054742341955250625 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 17 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-25271413646907723569938125 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R5S5 :
    OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (2 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (2 : Fin 9) (2 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R5S5Row0,
    originalYRowSplitD17R5S5Row1,
    originalYRowSplitD17R5S5Row2,
    originalYRowSplitD17R5S5Row3,
    originalYRowSplitD17R5S5Row4,
    originalYRowSplitD17R5S5Row5,
    originalYRowSplitD17R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
