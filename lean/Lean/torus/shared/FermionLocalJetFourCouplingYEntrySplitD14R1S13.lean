import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 14 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = (6583362741571577761800 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 14 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-99668087608688218394775 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 14 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((38696232435201326216055825 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 14 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-102606467765627934018585675 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 14 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((43314965565580414529141175 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 14 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-31840794610195342243940325 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 14 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2235032882227266950453625 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R1S13 :
    OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (0 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R1S13Row0,
    originalYRowSplitD14R1S13Row1,
    originalYRowSplitD14R1S13Row2,
    originalYRowSplitD14R1S13Row3,
    originalYRowSplitD14R1S13Row4,
    originalYRowSplitD14R1S13Row5,
    originalYRowSplitD14R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
