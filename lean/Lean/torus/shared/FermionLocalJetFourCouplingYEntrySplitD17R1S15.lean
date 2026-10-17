import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R1S15Row0 :
    OAI.Laughlin.Certificate.yRow 17 1 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S15Row1 :
    OAI.Laughlin.Certificate.yRow 17 1 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((207312153957520841604375 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S15Row2 :
    OAI.Laughlin.Certificate.yRow 17 1 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-81163659598754422217653125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S15Row3 :
    OAI.Laughlin.Certificate.yRow 17 1 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((1890970245824562240463125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S15Row4 :
    OAI.Laughlin.Certificate.yRow 17 1 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((154552990166839881822830625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S15Row5 :
    OAI.Laughlin.Certificate.yRow 17 1 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-8004271998183463118882390625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S15Row6 :
    OAI.Laughlin.Certificate.yRow 17 1 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-16649807394923920268926875 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R1S15 :
    OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (0 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 1 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R1S15Row0,
    originalYRowSplitD17R1S15Row1,
    originalYRowSplitD17R1S15Row2,
    originalYRowSplitD17R1S15Row3,
    originalYRowSplitD17R1S15Row4,
    originalYRowSplitD17R1S15Row5,
    originalYRowSplitD17R1S15Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R1S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
