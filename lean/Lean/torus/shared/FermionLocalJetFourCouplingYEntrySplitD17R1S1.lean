import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 17 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 17 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((23310757443028494214400625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 17 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((2029139579539363154754515625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 17 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((41313297259918227469550625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 17 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((-148272749931308533021421555625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 17 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-301867515108598122531600377625 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 17 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-66424649490151672527774091125 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R1S1 :
    OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (0 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (0 : Fin 9) (0 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R1S1Row0,
    originalYRowSplitD17R1S1Row1,
    originalYRowSplitD17R1S1Row2,
    originalYRowSplitD17R1S1Row3,
    originalYRowSplitD17R1S1Row4,
    originalYRowSplitD17R1S1Row5,
    originalYRowSplitD17R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
