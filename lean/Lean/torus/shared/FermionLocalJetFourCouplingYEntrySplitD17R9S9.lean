import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 17 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 17 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((87602083426030356225 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 17 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((122905306128511568025 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 17 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = (1380143549090941875450 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 17 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((791908698742853891763375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 17 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((5546850364312181257852575 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 17 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-778910400005671952857125 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R9S9 :
    OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (4 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R9S9Row0,
    originalYRowSplitD17R9S9Row1,
    originalYRowSplitD17R9S9Row2,
    originalYRowSplitD17R9S9Row3,
    originalYRowSplitD17R9S9Row4,
    originalYRowSplitD17R9S9Row5,
    originalYRowSplitD17R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
