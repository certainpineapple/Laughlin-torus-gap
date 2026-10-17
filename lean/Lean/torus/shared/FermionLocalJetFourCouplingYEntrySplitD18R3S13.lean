import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R3S13Row0 :
    OAI.Laughlin.Certificate.yRow 18 3 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S13Row1 :
    OAI.Laughlin.Certificate.yRow 18 3 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S13Row2 :
    OAI.Laughlin.Certificate.yRow 18 3 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S13Row3 :
    OAI.Laughlin.Certificate.yRow 18 3 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-2704598261431320234605625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S13Row4 :
    OAI.Laughlin.Certificate.yRow 18 3 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((127941556814423356260130875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S13Row5 :
    OAI.Laughlin.Certificate.yRow 18 3 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-88673002873302597487612875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S13Row6 :
    OAI.Laughlin.Certificate.yRow 18 3 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((105697268693393055681877875 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R3S13 :
    OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (1 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 3 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R3S13Row0,
    originalYRowSplitD18R3S13Row1,
    originalYRowSplitD18R3S13Row2,
    originalYRowSplitD18R3S13Row3,
    originalYRowSplitD18R3S13Row4,
    originalYRowSplitD18R3S13Row5,
    originalYRowSplitD18R3S13Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R3S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
