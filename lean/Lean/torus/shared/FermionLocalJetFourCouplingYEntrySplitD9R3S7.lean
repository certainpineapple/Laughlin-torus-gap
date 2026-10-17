import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 9 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((12183566695279863345 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 9 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-6655606365030085161 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 9 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-42187269918292356890115 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 9 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((2703157134167178053685 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 9 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-27563864112033776505 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 9 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((73431505991041509577815 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 9 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-225537941143045188945 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R3S7 :
    OAI.Laughlin.Certificate.errorRational 9 (1 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (1 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R3S7Row0,
    originalYRowSplitD9R3S7Row1,
    originalYRowSplitD9R3S7Row2,
    originalYRowSplitD9R3S7Row3,
    originalYRowSplitD9R3S7Row4,
    originalYRowSplitD9R3S7Row5,
    originalYRowSplitD9R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
