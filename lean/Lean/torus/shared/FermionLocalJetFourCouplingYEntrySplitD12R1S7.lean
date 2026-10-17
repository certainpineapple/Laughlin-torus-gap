import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 12 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-60800142901598533125 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 12 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((1296262290878134338825 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 12 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((1023236413332119466165675 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 12 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((315247942828983372810525 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 12 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-130526975606379086822175 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 12 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2149235804411346052163025 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 12 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-20765511048755247199425 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R1S7 :
    OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (0 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R1S7Row0,
    originalYRowSplitD12R1S7Row1,
    originalYRowSplitD12R1S7Row2,
    originalYRowSplitD12R1S7Row3,
    originalYRowSplitD12R1S7Row4,
    originalYRowSplitD12R1S7Row5,
    originalYRowSplitD12R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
