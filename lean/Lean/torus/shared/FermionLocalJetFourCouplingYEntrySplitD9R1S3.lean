import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 9 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-49935099302120812815 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 9 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-168340465635571388979 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 9 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((317820342725771002967205 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 9 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((5474468569476992474205 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 9 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-35192867316492751756425 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 9 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((40089004669018123382475 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 9 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((6391975394982420804645 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R1S3 :
    OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (1 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (0 : Fin 5) (1 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R1S3Row0,
    originalYRowSplitD9R1S3Row1,
    originalYRowSplitD9R1S3Row2,
    originalYRowSplitD9R1S3Row3,
    originalYRowSplitD9R1S3Row4,
    originalYRowSplitD9R1S3Row5,
    originalYRowSplitD9R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
