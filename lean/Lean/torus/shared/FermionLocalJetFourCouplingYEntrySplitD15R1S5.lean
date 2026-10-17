import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((389916641600646553267875 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((1730737715251315627481625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-2669623677541975007546067375 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-45539614182572824460020875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((483762039883419449708931375 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((4215607027385424494193995625 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-37392121137563250909976125 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S5 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (2 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (2 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S5Row0,
    originalYRowSplitD15R1S5Row1,
    originalYRowSplitD15R1S5Row2,
    originalYRowSplitD15R1S5Row3,
    originalYRowSplitD15R1S5Row4,
    originalYRowSplitD15R1S5Row5,
    originalYRowSplitD15R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
