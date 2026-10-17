import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 12 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-289381161197430015525 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 12 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((77586747202188781875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 12 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((178286563424254618204875 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 12 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((34281031240213244186175 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 12 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4655707091595102508875 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 12 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-54872127243116648728425 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 12 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-18586650000276144755325 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R3S7 :
    OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (1 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R3S7Row0,
    originalYRowSplitD12R3S7Row1,
    originalYRowSplitD12R3S7Row2,
    originalYRowSplitD12R3S7Row3,
    originalYRowSplitD12R3S7Row4,
    originalYRowSplitD12R3S7Row5,
    originalYRowSplitD12R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
