import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 15 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = (63993984141912764625 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 15 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((6455931361239631721625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 15 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1338810119094327996099375 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 15 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((54083159190104735494125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 15 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((4126969138342666553276625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 15 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((8696882985571431424657125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 15 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-219449727095530612739625 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R5S9 :
    OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (2 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R5S9Row0,
    originalYRowSplitD15R5S9Row1,
    originalYRowSplitD15R5S9Row2,
    originalYRowSplitD15R5S9Row3,
    originalYRowSplitD15R5S9Row4,
    originalYRowSplitD15R5S9Row5,
    originalYRowSplitD15R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
