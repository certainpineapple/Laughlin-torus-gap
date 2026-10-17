import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 20 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 20 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 20 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 20 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 20 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-99685520110442588481534375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 20 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = (-16825486649640669041666625 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 20 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((2781530893336920858948189375 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R1S13 :
    OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (6 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (0 : Fin 10) (6 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R1S13Row0,
    originalYRowSplitD20R1S13Row1,
    originalYRowSplitD20R1S13Row2,
    originalYRowSplitD20R1S13Row3,
    originalYRowSplitD20R1S13Row4,
    originalYRowSplitD20R1S13Row5,
    originalYRowSplitD20R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
