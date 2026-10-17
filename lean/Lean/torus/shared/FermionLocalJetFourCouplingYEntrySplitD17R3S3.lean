import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 17 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 17 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((2904536411797224654675225 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 17 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((86831692166142042270176025 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 17 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((112827923202375246163723425 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 17 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((7619961848183047498012052175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 17 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-14980037975335986053378152275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 17 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-64026932377361005714887225 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R3S3 :
    OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (1 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (1 : Fin 9) (1 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R3S3Row0,
    originalYRowSplitD17R3S3Row1,
    originalYRowSplitD17R3S3Row2,
    originalYRowSplitD17R3S3Row3,
    originalYRowSplitD17R3S3Row4,
    originalYRowSplitD17R3S3Row5,
    originalYRowSplitD17R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
