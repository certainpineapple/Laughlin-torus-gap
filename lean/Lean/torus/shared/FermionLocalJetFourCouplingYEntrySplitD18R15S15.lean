import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R15S15Row0 :
    OAI.Laughlin.Certificate.yRow 18 15 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R15S15Row1 :
    OAI.Laughlin.Certificate.yRow 18 15 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R15S15Row2 :
    OAI.Laughlin.Certificate.yRow 18 15 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R15S15Row3 :
    OAI.Laughlin.Certificate.yRow 18 15 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((486468517620763933880625 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R15S15Row4 :
    OAI.Laughlin.Certificate.yRow 18 15 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((28332491553328079101359375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R15S15Row5 :
    OAI.Laughlin.Certificate.yRow 18 15 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((377364906205749703375509375 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R15S15Row6 :
    OAI.Laughlin.Certificate.yRow 18 15 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R15S15 :
    OAI.Laughlin.Certificate.errorRational 18 (7 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (7 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 15 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R15S15Row0,
    originalYRowSplitD18R15S15Row1,
    originalYRowSplitD18R15S15Row2,
    originalYRowSplitD18R15S15Row3,
    originalYRowSplitD18R15S15Row4,
    originalYRowSplitD18R15S15Row5,
    originalYRowSplitD18R15S15Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R15S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
