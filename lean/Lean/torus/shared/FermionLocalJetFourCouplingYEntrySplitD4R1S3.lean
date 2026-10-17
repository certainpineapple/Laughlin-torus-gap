import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD4R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 4 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1050629001181122255 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 4 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3968381080127179827 / 2348810240) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 4 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-12339595641602182873749 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 4 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((20920915038933275615163 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 4 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2509784308894817097541 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 4 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-228592658543344939975 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 4 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-17657764371566617689 / 134217728) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD4R1S3 :
    OAI.Laughlin.Certificate.errorRational 4 (0 : Fin 2) (1 : Fin 2) =
      TorusLean.FermionM3.errorTable04 (0 : Fin 2) (1 : Fin 2) := by
  change OAI.Laughlin.Certificate.Y 4 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD4R1S3Row0,
    originalYRowSplitD4R1S3Row1,
    originalYRowSplitD4R1S3Row2,
    originalYRowSplitD4R1S3Row3,
    originalYRowSplitD4R1S3Row4,
    originalYRowSplitD4R1S3Row5,
    originalYRowSplitD4R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable04]

#print axioms originalYEntrySplitD4R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
