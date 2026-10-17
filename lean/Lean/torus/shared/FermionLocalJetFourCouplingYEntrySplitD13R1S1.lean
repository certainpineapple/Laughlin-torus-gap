import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 13 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((-235505922442572329804025 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 13 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((-614415638583882352218375 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 13 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((1591609317461808701829663825 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 13 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((-262150294219171137976717125 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 13 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((-5005226768330375130745575 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 13 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2565035428169218737009105675 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 13 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1893391850538294645040425 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R1S1 :
    OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (0 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (0 : Fin 7) (0 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R1S1Row0,
    originalYRowSplitD13R1S1Row1,
    originalYRowSplitD13R1S1Row2,
    originalYRowSplitD13R1S1Row3,
    originalYRowSplitD13R1S1Row4,
    originalYRowSplitD13R1S1Row5,
    originalYRowSplitD13R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable13]


#print axioms originalYEntrySplitD13R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
