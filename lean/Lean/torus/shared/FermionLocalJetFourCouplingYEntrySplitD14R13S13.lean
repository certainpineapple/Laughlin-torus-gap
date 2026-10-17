import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R13S13Row0 :
    OAI.Laughlin.Certificate.yRow 14 13 13
      (OAI.Laughlin.Certificate.rows[0]!) = (3008235531803330228400 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R13S13Row1 :
    OAI.Laughlin.Certificate.yRow 14 13 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-1541649559149037713375 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R13S13Row2 :
    OAI.Laughlin.Certificate.yRow 14 13 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((4035341750414418695876625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R13S13Row3 :
    OAI.Laughlin.Certificate.yRow 14 13 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((4688751520673428572389025 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R13S13Row4 :
    OAI.Laughlin.Certificate.yRow 14 13 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((7685543103280590711574125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R13S13Row5 :
    OAI.Laughlin.Certificate.yRow 14 13 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-13398201486726893579746575 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R13S13Row6 :
    OAI.Laughlin.Certificate.yRow 14 13 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-6933800034828779337225 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R13S13 :
    OAI.Laughlin.Certificate.errorRational 14 (6 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (6 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 13 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R13S13Row0,
    originalYRowSplitD14R13S13Row1,
    originalYRowSplitD14R13S13Row2,
    originalYRowSplitD14R13S13Row3,
    originalYRowSplitD14R13S13Row4,
    originalYRowSplitD14R13S13Row5,
    originalYRowSplitD14R13S13Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R13S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
