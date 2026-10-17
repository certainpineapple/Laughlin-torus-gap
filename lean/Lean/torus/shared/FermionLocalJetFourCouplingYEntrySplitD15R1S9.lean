import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((100250525927899641068775 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-730208003634378289995975 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-562428689800030984509353775 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-16917738371565448461018975 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((55714222532759700634349625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-186429369361810134072588075 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1250926487940087065282175 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S9 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S9Row0,
    originalYRowSplitD15R1S9Row1,
    originalYRowSplitD15R1S9Row2,
    originalYRowSplitD15R1S9Row3,
    originalYRowSplitD15R1S9Row4,
    originalYRowSplitD15R1S9Row5,
    originalYRowSplitD15R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
