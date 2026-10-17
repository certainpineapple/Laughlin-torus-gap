import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 13 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (37537242385159271475 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 13 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((67239507499443120825 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 13 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((83778058415794161130065 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 13 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((31798913273157348758475 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 13 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-10602708279829947506385 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 13 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-64676644823080258719165 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 13 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-7424698753468983999285 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R9S9 :
    OAI.Laughlin.Certificate.errorRational 13 (4 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (4 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R9S9Row0,
    originalYRowSplitD13R9S9Row1,
    originalYRowSplitD13R9S9Row2,
    originalYRowSplitD13R9S9Row3,
    originalYRowSplitD13R9S9Row4,
    originalYRowSplitD13R9S9Row5,
    originalYRowSplitD13R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
