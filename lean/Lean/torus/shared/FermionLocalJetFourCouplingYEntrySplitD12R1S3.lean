import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 12 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-8802694327103294465925 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 12 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-4460364066878174420955 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 12 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5884572682445203329103125 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 12 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-750254352190999663186575 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 12 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((2422456589957648729054625 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 12 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((718970303937414452202675 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 12 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-81169077257917756967475 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R1S3 :
    OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (1 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (0 : Fin 6) (1 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R1S3Row0,
    originalYRowSplitD12R1S3Row1,
    originalYRowSplitD12R1S3Row2,
    originalYRowSplitD12R1S3Row3,
    originalYRowSplitD12R1S3Row4,
    originalYRowSplitD12R1S3Row5,
    originalYRowSplitD12R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
