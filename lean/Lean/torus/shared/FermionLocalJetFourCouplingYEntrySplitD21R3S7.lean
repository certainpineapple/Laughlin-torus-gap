import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 21 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 21 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 21 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 21 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 21 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((63039081108652064122960378125 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 21 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((71570878950453883612486875 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 21 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1268516598703590993389758125 / 16) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R3S7 :
    OAI.Laughlin.Certificate.errorRational 21 (1 : Fin 11) (3 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (1 : Fin 11) (3 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R3S7Row0,
    originalYRowSplitD21R3S7Row1,
    originalYRowSplitD21R3S7Row2,
    originalYRowSplitD21R3S7Row3,
    originalYRowSplitD21R3S7Row4,
    originalYRowSplitD21R3S7Row5,
    originalYRowSplitD21R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
