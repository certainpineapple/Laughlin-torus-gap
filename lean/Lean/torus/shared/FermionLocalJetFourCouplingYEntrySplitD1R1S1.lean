import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD1R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 1 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((656013083261437533 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD1R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 1 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((338859671956552637039 / 37580963840) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD1R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 1 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((135489255573548222798955 / 30064771072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD1R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 1 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((8237963323220102233749 / 7516192768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD1R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 1 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((987900274842154761509 / 90194313216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD1R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 1 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((224626130525559249025199 / 51539607552) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD1R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 1 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-640875948582138093563 / 2147483648) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD1R1S1 :
    OAI.Laughlin.Certificate.errorRational 1 (0 : Fin 1) (0 : Fin 1) =
      TorusLean.FermionM3.errorTable01 (0 : Fin 1) (0 : Fin 1) := by
  change OAI.Laughlin.Certificate.Y 1 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD1R1S1Row0,
    originalYRowSplitD1R1S1Row1,
    originalYRowSplitD1R1S1Row2,
    originalYRowSplitD1R1S1Row3,
    originalYRowSplitD1R1S1Row4,
    originalYRowSplitD1R1S1Row5,
    originalYRowSplitD1R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable01]

#print axioms originalYEntrySplitD1R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
