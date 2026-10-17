import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 16 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1710110859762941953542225 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 16 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-39318177815407349483625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 16 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((47167473767314048956232425 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 16 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((1314817683628625650086037425 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 16 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-237129485443752063291675975 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 16 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((143883898794037369796303475 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 16 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1696653672746245310340017775 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R3S3 :
    OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (1 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (1 : Fin 8) (1 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R3S3Row0,
    originalYRowSplitD16R3S3Row1,
    originalYRowSplitD16R3S3Row2,
    originalYRowSplitD16R3S3Row3,
    originalYRowSplitD16R3S3Row4,
    originalYRowSplitD16R3S3Row5,
    originalYRowSplitD16R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
