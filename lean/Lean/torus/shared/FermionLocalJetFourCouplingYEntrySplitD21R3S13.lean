import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R3S13Row0 :
    OAI.Laughlin.Certificate.yRow 21 3 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S13Row1 :
    OAI.Laughlin.Certificate.yRow 21 3 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S13Row2 :
    OAI.Laughlin.Certificate.yRow 21 3 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S13Row3 :
    OAI.Laughlin.Certificate.yRow 21 3 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S13Row4 :
    OAI.Laughlin.Certificate.yRow 21 3 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((48254831933804315109415125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S13Row5 :
    OAI.Laughlin.Certificate.yRow 21 3 13
      (OAI.Laughlin.Certificate.rows[5]!) = (-18334655209249624941696000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S13Row6 :
    OAI.Laughlin.Certificate.yRow 21 3 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((36243331391531171239707375 / 2) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R3S13 :
    OAI.Laughlin.Certificate.errorRational 21 (1 : Fin 11) (6 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (1 : Fin 11) (6 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 3 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R3S13Row0,
    originalYRowSplitD21R3S13Row1,
    originalYRowSplitD21R3S13Row2,
    originalYRowSplitD21R3S13Row3,
    originalYRowSplitD21R3S13Row4,
    originalYRowSplitD21R3S13Row5,
    originalYRowSplitD21R3S13Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R3S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
