import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R13S15Row0 :
    OAI.Laughlin.Certificate.yRow 17 13 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S15Row1 :
    OAI.Laughlin.Certificate.yRow 17 13 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-461350194993624061125 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S15Row2 :
    OAI.Laughlin.Certificate.yRow 17 13 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-900165023112560069489625 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S15Row3 :
    OAI.Laughlin.Certificate.yRow 17 13 15
      (OAI.Laughlin.Certificate.rows[3]!) = (213612842441771428280625 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S15Row4 :
    OAI.Laughlin.Certificate.yRow 17 13 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((29477381811489708818596875 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S15Row5 :
    OAI.Laughlin.Certificate.yRow 17 13 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((24814701260280613760203125 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R13S15Row6 :
    OAI.Laughlin.Certificate.yRow 17 13 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R13S15 :
    OAI.Laughlin.Certificate.errorRational 17 (6 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (6 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 13 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R13S15Row0,
    originalYRowSplitD17R13S15Row1,
    originalYRowSplitD17R13S15Row2,
    originalYRowSplitD17R13S15Row3,
    originalYRowSplitD17R13S15Row4,
    originalYRowSplitD17R13S15Row5,
    originalYRowSplitD17R13S15Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R13S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
