import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((5463419794124310458455640625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((-45798992581501900846944964125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1347493392181974604556580215625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-116154927885677201764740622125 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S1 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (0 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (0 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S1Row0,
    originalYRowSplitD18R1S1Row1,
    originalYRowSplitD18R1S1Row2,
    originalYRowSplitD18R1S1Row3,
    originalYRowSplitD18R1S1Row4,
    originalYRowSplitD18R1S1Row5,
    originalYRowSplitD18R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
