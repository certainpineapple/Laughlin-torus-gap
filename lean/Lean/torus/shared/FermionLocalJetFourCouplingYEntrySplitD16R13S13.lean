import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R13S13Row0 :
    OAI.Laughlin.Certificate.yRow 16 13 13
      (OAI.Laughlin.Certificate.rows[0]!) = (5439250947632261760000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S13Row1 :
    OAI.Laughlin.Certificate.yRow 16 13 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((37041441713207056125 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S13Row2 :
    OAI.Laughlin.Certificate.yRow 16 13 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((43301346233755422287475 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S13Row3 :
    OAI.Laughlin.Certificate.yRow 16 13 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((7802187035416273488213225 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S13Row4 :
    OAI.Laughlin.Certificate.yRow 16 13 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((10861516433332026792126225 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S13Row5 :
    OAI.Laughlin.Certificate.yRow 16 13 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-30891077170573311298453275 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S13Row6 :
    OAI.Laughlin.Certificate.yRow 16 13 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-19727702108397082124325 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R13S13 :
    OAI.Laughlin.Certificate.errorRational 16 (6 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (6 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 13 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R13S13Row0,
    originalYRowSplitD16R13S13Row1,
    originalYRowSplitD16R13S13Row2,
    originalYRowSplitD16R13S13Row3,
    originalYRowSplitD16R13S13Row4,
    originalYRowSplitD16R13S13Row5,
    originalYRowSplitD16R13S13Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R13S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
