import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 11 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-222421445513167044375 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 11 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((486934588724303163555 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 11 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((6684832913531000666488875 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 11 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((465146098048009324577925 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 11 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((131947869228104863833075 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 11 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-4292361742031574796798425 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 11 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((4012144119936168052725 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R1S7 :
    OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (0 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R1S7Row0,
    originalYRowSplitD11R1S7Row1,
    originalYRowSplitD11R1S7Row2,
    originalYRowSplitD11R1S7Row3,
    originalYRowSplitD11R1S7Row4,
    originalYRowSplitD11R1S7Row5,
    originalYRowSplitD11R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
