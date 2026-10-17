import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 11 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((255118613033705600025 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 11 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((1345560530284334986875 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 11 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((16517634948434468322819675 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 11 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((1063259930285177824774575 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 11 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((199171759334488794124425 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 11 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((2175498342092874003378525 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 11 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1291195132370023263075 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R11S11 :
    OAI.Laughlin.Certificate.errorRational 11 (5 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (5 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R11S11Row0,
    originalYRowSplitD11R11S11Row1,
    originalYRowSplitD11R11S11Row2,
    originalYRowSplitD11R11S11Row3,
    originalYRowSplitD11R11S11Row4,
    originalYRowSplitD11R11S11Row5,
    originalYRowSplitD11R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
