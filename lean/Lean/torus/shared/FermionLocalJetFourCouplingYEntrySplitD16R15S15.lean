import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R15S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 15 15
      (OAI.Laughlin.Certificate.rows[0]!) = (87843171603385958760000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R15S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 15 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((1843712255320140830625 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R15S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 15 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((3246469442460889900880625 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R15S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 15 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((28336418693411150192495625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R15S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 15 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((6724673423792675226500625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R15S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 15 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((68463730171339470385543125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R15S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 15 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R15S15 :
    OAI.Laughlin.Certificate.errorRational 16 (7 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (7 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 15 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R15S15Row0,
    originalYRowSplitD16R15S15Row1,
    originalYRowSplitD16R15S15Row2,
    originalYRowSplitD16R15S15Row3,
    originalYRowSplitD16R15S15Row4,
    originalYRowSplitD16R15S15Row5,
    originalYRowSplitD16R15S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R15S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
