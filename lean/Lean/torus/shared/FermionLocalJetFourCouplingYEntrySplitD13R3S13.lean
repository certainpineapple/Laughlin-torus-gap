import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R3S13Row0 :
    OAI.Laughlin.Certificate.yRow 13 3 13
      (OAI.Laughlin.Certificate.rows[0]!) = ((2114267310189937027125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S13Row1 :
    OAI.Laughlin.Certificate.yRow 13 3 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((8293103871971759723025 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S13Row2 :
    OAI.Laughlin.Certificate.yRow 13 3 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-4682688277201479002375775 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S13Row3 :
    OAI.Laughlin.Certificate.yRow 13 3 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1577211755607576090577575 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S13Row4 :
    OAI.Laughlin.Certificate.yRow 13 3 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((4823185327101912139694325 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S13Row5 :
    OAI.Laughlin.Certificate.yRow 13 3 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((1969865939573988936962625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S13Row6 :
    OAI.Laughlin.Certificate.yRow 13 3 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((110587542413780388431475 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R3S13 :
    OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (1 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 3 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R3S13Row0,
    originalYRowSplitD13R3S13Row1,
    originalYRowSplitD13R3S13Row2,
    originalYRowSplitD13R3S13Row3,
    originalYRowSplitD13R3S13Row4,
    originalYRowSplitD13R3S13Row5,
    originalYRowSplitD13R3S13Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R3S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
