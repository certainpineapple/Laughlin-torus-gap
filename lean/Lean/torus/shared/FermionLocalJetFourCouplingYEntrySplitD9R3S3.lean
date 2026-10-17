import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 9 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-3920649302160314055 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 9 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((60817996064624161491 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 9 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-83031928993007233433235 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 9 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((11365116761282300837865 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 9 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((72263184132468784672395 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 9 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-937196838343730181186135 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 9 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-7977566760994191833775 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R3S3 :
    OAI.Laughlin.Certificate.errorRational 9 (1 : Fin 5) (1 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (1 : Fin 5) (1 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R3S3Row0,
    originalYRowSplitD9R3S3Row1,
    originalYRowSplitD9R3S3Row2,
    originalYRowSplitD9R3S3Row3,
    originalYRowSplitD9R3S3Row4,
    originalYRowSplitD9R3S3Row5,
    originalYRowSplitD9R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
