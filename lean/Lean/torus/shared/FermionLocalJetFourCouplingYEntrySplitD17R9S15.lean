import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R9S15Row0 :
    OAI.Laughlin.Certificate.yRow 17 9 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S15Row1 :
    OAI.Laughlin.Certificate.yRow 17 9 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((401886843283217667375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S15Row2 :
    OAI.Laughlin.Certificate.yRow 17 9 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-19975192631424457552125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S15Row3 :
    OAI.Laughlin.Certificate.yRow 17 9 15
      (OAI.Laughlin.Certificate.rows[3]!) = (-12037954918346371389375 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S15Row4 :
    OAI.Laughlin.Certificate.yRow 17 9 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4860637727089277690431875 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S15Row5 :
    OAI.Laughlin.Certificate.yRow 17 9 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-58235880408370282160668125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S15Row6 :
    OAI.Laughlin.Certificate.yRow 17 9 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-48965890395869513191125 / 16) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R9S15 :
    OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (4 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 9 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R9S15Row0,
    originalYRowSplitD17R9S15Row1,
    originalYRowSplitD17R9S15Row2,
    originalYRowSplitD17R9S15Row3,
    originalYRowSplitD17R9S15Row4,
    originalYRowSplitD17R9S15Row5,
    originalYRowSplitD17R9S15Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R9S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
