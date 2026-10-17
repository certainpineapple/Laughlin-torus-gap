import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((25042994223357808423600875 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3197662202891439493835625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-277191003513418064493798375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-4565794748354665000652602125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-769344449913388857550667625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((2306039119601161660449859125 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1504502456641797728217477375 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S3 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (1 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (1 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S3Row0,
    originalYRowSplitD16R1S3Row1,
    originalYRowSplitD16R1S3Row2,
    originalYRowSplitD16R1S3Row3,
    originalYRowSplitD16R1S3Row4,
    originalYRowSplitD16R1S3Row5,
    originalYRowSplitD16R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
