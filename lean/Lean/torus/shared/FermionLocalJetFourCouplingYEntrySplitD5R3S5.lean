import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD5R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 5 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((2088880360412782875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 5 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((9078017688703880489 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 5 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((4154519314999427044985 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 5 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1676596742006268315615 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 5 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((1122516649266680657945 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 5 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((11113921888615690197695 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 5 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-125595578390684976075 / 67108864) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD5R3S5 :
    OAI.Laughlin.Certificate.errorRational 5 (1 : Fin 3) (2 : Fin 3) =
      TorusLean.FermionM3.errorTable05 (1 : Fin 3) (2 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 5 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD5R3S5Row0,
    originalYRowSplitD5R3S5Row1,
    originalYRowSplitD5R3S5Row2,
    originalYRowSplitD5R3S5Row3,
    originalYRowSplitD5R3S5Row4,
    originalYRowSplitD5R3S5Row5,
    originalYRowSplitD5R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable05]

#print axioms originalYEntrySplitD5R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
