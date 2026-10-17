import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 12 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-476012474831698479675 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 12 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-1197953574428834846865 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 12 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((1753760732940640676461275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 12 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((5128248610909246000684275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 12 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-108726317371792211352525 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 12 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((2959749673587125942665725 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 12 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((5693785160289628299975 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R1S9 :
    OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (0 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R1S9Row0,
    originalYRowSplitD12R1S9Row1,
    originalYRowSplitD12R1S9Row2,
    originalYRowSplitD12R1S9Row3,
    originalYRowSplitD12R1S9Row4,
    originalYRowSplitD12R1S9Row5,
    originalYRowSplitD12R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
