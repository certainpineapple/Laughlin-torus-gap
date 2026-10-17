import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 17 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 17 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3683144911808337215625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 17 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((1892429216683889540146875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 17 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((433665895178181611570625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 17 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((2243737273318021380796875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 17 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-128498251511088969906763125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 17 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1429951919397038454965625 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R5S11 :
    OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (2 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R5S11Row0,
    originalYRowSplitD17R5S11Row1,
    originalYRowSplitD17R5S11Row2,
    originalYRowSplitD17R5S11Row3,
    originalYRowSplitD17R5S11Row4,
    originalYRowSplitD17R5S11Row5,
    originalYRowSplitD17R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
