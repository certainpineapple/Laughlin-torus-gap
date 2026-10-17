import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 17 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 17 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((135466431277041104625 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 17 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-6696867541735102606875 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 17 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((12591741958560624061125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 17 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-56094121405789831893375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 17 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-10054394164135638975475125 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 17 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-299185573522912794592875 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R9S11 :
    OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (4 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R9S11Row0,
    originalYRowSplitD17R9S11Row1,
    originalYRowSplitD17R9S11Row2,
    originalYRowSplitD17R9S11Row3,
    originalYRowSplitD17R9S11Row4,
    originalYRowSplitD17R9S11Row5,
    originalYRowSplitD17R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
