import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 15 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-4584744890144758109925 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 15 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-15295943833737513182775 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 15 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((10558179375165475036639425 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 15 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-3562775251252040826473625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 15 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2638467423618078012416775 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 15 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-17947393929724452504886575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 15 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((126883810408473066581325 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R3S9 :
    OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (1 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R3S9Row0,
    originalYRowSplitD15R3S9Row1,
    originalYRowSplitD15R3S9Row2,
    originalYRowSplitD15R3S9Row3,
    originalYRowSplitD15R3S9Row4,
    originalYRowSplitD15R3S9Row5,
    originalYRowSplitD15R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
