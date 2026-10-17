import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 8 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((1990312643635120665 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 8 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-1095344391635191101 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 8 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((11311749600528369600555 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 8 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((8603647500660654488295 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 8 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((3519874183592373572895 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 8 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-3479431231969799395785 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 8 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((672523966016989221555 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R3S7 :
    OAI.Laughlin.Certificate.errorRational 8 (1 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (1 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R3S7Row0,
    originalYRowSplitD8R3S7Row1,
    originalYRowSplitD8R3S7Row2,
    originalYRowSplitD8R3S7Row3,
    originalYRowSplitD8R3S7Row4,
    originalYRowSplitD8R3S7Row5,
    originalYRowSplitD8R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
