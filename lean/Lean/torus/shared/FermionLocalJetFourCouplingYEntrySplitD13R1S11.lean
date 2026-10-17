import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 13 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-8579099438890977894975 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 13 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((1793766965491743924825 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 13 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-58543692825518825363834175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 13 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-3105448856429425803695475 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 13 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1042328701442842909957125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 13 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-17565229985784795303093225 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 13 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-75628442229949799484525 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R1S11 :
    OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (0 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R1S11Row0,
    originalYRowSplitD13R1S11Row1,
    originalYRowSplitD13R1S11Row2,
    originalYRowSplitD13R1S11Row3,
    originalYRowSplitD13R1S11Row4,
    originalYRowSplitD13R1S11Row5,
    originalYRowSplitD13R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
